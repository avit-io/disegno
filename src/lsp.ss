;; Il server LSP: disegno lsp. JSON-RPC su stdin/stdout, con le intestazioni Content-Length.
;; Diagnostica all'apertura, a ogni modifica e al salvataggio: il testo del documento si controlla
;; in un processo a sé (disegno check), così ogni controllo parte pulito; ogni riga d'errore
;; file:riga:colonna: messaggio diventa una diagnostica. Si legge e si scrive in byte:
;; Content-Length conta byte, non caratteri.
;; Hover: il tipo del nome globale sotto il cursore (disegno type). Definizione: dove è definito
;; (disegno where), anche nella libreria standard. Simboli: le dichiarazioni del file.
;; ponytail: hover e definizione solo per i nomi globali; le variabili locali verranno se servono.

(define lsp-in (standard-input-port))
(define lsp-out (standard-output-port))

(define (read-message)                                   ; → oggetto JSON, o #f a fine input
  (let loop ([len #f])
    (let ([line (read-header-line)])
      (cond [(not line) #f]
            [(string=? line "") (and len (json-read (utf8->string (get-bytevector-n lsp-in len))))]
            [(and (> (string-length line) 15) (string-ci=? (substring line 0 15) "content-length:"))
             (loop (string->number (string-trim (substring line 15 (string-length line)))))]
            [else (loop len)]))))

(define (read-header-line)                               ; una riga di intestazione, senza \r\n
  (let loop ([acc '()])
    (let ([b (get-u8 lsp-in)])
      (cond [(eof-object? b) (and (pair? acc) (list->string (reverse acc)))]
            [(= b 10) (list->string (reverse (if (and (pair? acc) (char=? (car acc) #\return)) (cdr acc) acc)))]
            [else (loop (cons (integer->char b) acc))]))))

(define (string-trim s)
  (let* ([cs (string->list s)] [drop (lambda (cs) (let loop ([cs cs]) (if (and (pair? cs) (char-whitespace? (car cs))) (loop (cdr cs)) cs)))])
    (list->string (reverse (drop (reverse (drop cs)))))))

(define (send v)
  (let ([body (string->utf8 (json->string v))])
    (put-bytevector lsp-out (string->utf8 (format "Content-Length: ~a\r\n\r\n" (bytevector-length body))))
    (put-bytevector lsp-out body)
    (flush-output-port lsp-out)))

(define (get o k) (let ([p (and (pair? o) (assoc k o))]) (and p (cdr p))))

(define (respond msg result) (send `(("jsonrpc" . "2.0") ("id" . ,(get msg "id")) ("result" . ,result))))

(define (position line col) `(("line" . ,line) ("character" . ,col)))
(define (range line col) `(("start" . ,(position line col)) ("end" . ,(position line (+ col 1)))))

;; --- il documento in un processo a sé ---

(define documents (make-hashtable string-hash string=?))  ; uri → testo

(define (uri->path uri) (if (and (> (string-length uri) 7) (string=? (substring uri 0 7) "file://")) (substring uri 7 (string-length uri)) uri))

(define scheme-bin (or (getenv "DISEGNO_SCHEME") "scheme"))

;; Il testo in un file temporaneo, poi disegno <args…> sul file; → (stdout stderr successo?)
(define (run-on text . args)
  (let* ([tmp (format "/tmp/disegno-lsp-~a.disegno" (random 1000000000))]
         [out (string-append tmp ".out")] [err (string-append tmp ".err")])
    (call-with-output-file tmp (lambda (p) (put-string p text)) 'replace)
    (let* ([ok (zero? (system (format "~a --script ~a ~a ~a ~a >~a 2>~a" scheme-bin (at-root "src/main.ss")
                                      (car args) tmp (apply string-append (map (lambda (a) (format "'~a' " a)) (cdr args))) out err)))]
           [slurp (lambda (f) (let ([s (call-with-input-file f get-string-all)]) (delete-file f) (if (eof-object? s) "" s)))]
           [r (list tmp (slurp out) (slurp err) ok)])
      (delete-file tmp)
      r)))

;; "file:riga:colonna: messaggio" → (file riga colonna messaggio), o #f
(define (parse-location s)
  (let ([parts (split-on s #\:)])
    (and (>= (length parts) 3) (string->number (cadr parts)) (string->number (caddr parts))
         (let ([k (+ 3 (string-length (car parts)) (string-length (cadr parts)) (string-length (caddr parts)))])
           (list (car parts) (string->number (cadr parts)) (string->number (caddr parts))
                 (if (> (string-length s) k) (string-trim (substring s k (string-length s))) ""))))))

(define (lines s) (filter (lambda (l) (not (string=? l ""))) (split-on s #\newline)))

;; --- diagnostica ---

(define (publish-diagnostics uri)
  (let* ([r (run-on (hashtable-ref documents uri "") "check")] [tmp (car r)]
         [errs (filter (lambda (e) (and e (string=? (car e) tmp))) (map parse-location (lines (caddr r))))])   ; solo gli errori di questo file
    (send `(("jsonrpc" . "2.0") ("method" . "textDocument/publishDiagnostics")
            ("params" . (("uri" . ,uri)
                         ("diagnostics" . ,(list->vector (map (lambda (e) `(("range" . ,(range (- (cadr e) 1) (- (caddr e) 1)))
                                                                             ("severity" . 1) ("source" . "disegno") ("message" . ,(cadddr e))))
                                                              errs)))))))))

;; --- il nome sotto il cursore ---

(define (word-at text line character)                    ; il simbolo che contiene la posizione, o #f
  (let* ([lines (split-on text #\newline)]
         [s (and (< line (length lines)) (list-ref lines line))])
    (and s
         (let* ([delim? (lambda (c) (or (char-whitespace? c) (memv c '(#\( #\) #\[ #\] #\{ #\} #\; #\, #\"))))]
                [n (string-length s)] [i (min character n)]
                [start (let loop ([j i]) (if (and (> j 0) (not (delim? (string-ref s (- j 1))))) (loop (- j 1)) j))]
                [end (let loop ([j i]) (if (and (< j n) (not (delim? (string-ref s j)))) (loop (+ j 1)) j))])
           (and (< start end) (substring s start end))))))

(define (word-of params)
  (let* ([pos (get params "position")]
         [w (word-at (hashtable-ref documents (get (get params "textDocument") "uri") "") (get pos "line") (get pos "character"))])
    (and w (not (memv #\' (string->list w))) w)))

;; Hover: il tipo, con le varianti dei nomi corti.
(define (hover msg params)
  (let* ([uri (get (get params "textDocument") "uri")] [word (word-of params)]
         [r (and word (run-on (hashtable-ref documents uri "") "type" word))])
    (respond msg (if (and r (cadddr r))
                     `(("contents" . (("kind" . "markdown") ("value" . ,(string-append "```disegno\n" (cadr r) "```")))))
                     'null))))

;; Definizione: dove sta, nel documento stesso o in un file della libreria.
(define (definition msg params)
  (let* ([uri (get (get params "textDocument") "uri")] [word (word-of params)]
         [r (and word (run-on (hashtable-ref documents uri "") "where" word))]
         [abs (lambda (f) (if (and (> (string-length f) 0) (char=? (string-ref f 0) #\/)) f (string-append (current-directory) "/" f)))])
    (respond msg (if (and r (cadddr r))
                     (list->vector
                       (map (lambda (l) `(("uri" . ,(if (string=? (car l) (car r)) uri (string-append "file://" (abs (car l)))))
                                          ("range" . ,(range (- (cadr l) 1) (- (caddr l) 1)))))
                            (filter values (map parse-location (lines (cadr r))))))
                     'null))))

;; --- simboli: le dichiarazioni del file, lette senza controllarle ---

(define symbol-kinds '((def . 12) (data . 10) (record . 23) (extern . 12)))   ; Function, Enum, Struct

(define (document-symbols msg params)
  (let*-values ([(text) (hashtable-ref documents (get (get params "textDocument") "uri") "")]
                [(t opens) (brackets text)])
    (let* ([sfd (make-source-file-descriptor "doc" (open-bytevector-input-port (string->utf8 t)))]
           [p (open-string-input-port t)]
           [line-col (lambda (off)                    ; offset → (riga . colonna), da 0
                       (let loop ([i 0] [l 0] [c 0])
                         (if (>= i off) (cons l c) (if (char=? (string-ref text i) #\newline) (loop (+ i 1) (+ l 1) 0) (loop (+ i 1) l (+ c 1))))))]
           [decls (guard (e [#t '()])                   ; un testo a metà: i simboli letti fin lì
                    (let loop ([bfp 0] [acc '()])
                      (let-values ([(a next) (guard (e [#t (values (eof-object) bfp)]) (get-datum/annotations p sfd bfp))])
                        (if (eof-object? a) (reverse acc) (loop next (cons a acc))))))])
      (respond msg
        (list->vector
          (filter values
            (map (lambda (a)
                   (let* ([e (annotation-stripped a)] [k (and (pair? e) (assq (car e) symbol-kinds))])
                     (and k (pair? (cdr e))
                          (let* ([n (cadr e)] [n (if (pair? n) (car n) n)]
                                 [s (line-col (source-object-bfp (annotation-source a)))]
                                 [f (line-col (source-object-efp (annotation-source a)))]
                                 [r `(("start" . ,(position (car s) (cdr s))) ("end" . ,(position (car f) (cdr f))))])
                            (and (symbol? n)
                                 `(("name" . ,(symbol->string n)) ("kind" . ,(cdr k)) ("range" . ,r) ("selectionRange" . ,r)))))))
                 decls)))))))

;; --- il ciclo ---

(define (serve)
  (let loop ()
    (let ([msg (read-message)])
      (when msg
        (let ([method (get msg "method")] [params (get msg "params")])
          (cond
            [(equal? method "initialize")
             (respond msg `(("capabilities" . (("textDocumentSync" . (("openClose" . #t) ("change" . 1) ("save" . #t)))
                                               ("hoverProvider" . #t) ("definitionProvider" . #t) ("documentSymbolProvider" . #t)))
                            ("serverInfo" . (("name" . "disegno")))))]
            [(equal? method "textDocument/didOpen")
             (let ([doc (get params "textDocument")])
               (hashtable-set! documents (get doc "uri") (get doc "text"))
               (publish-diagnostics (get doc "uri")))]
            [(equal? method "textDocument/didChange")      ; si controlla solo se non arriva già altro
             (let ([uri (get (get params "textDocument") "uri")] [changes (get params "contentChanges")])
               (when (pair? changes)
                 (hashtable-set! documents uri (get (car (last-pair changes)) "text")))
               (unless (input-port-ready? lsp-in) (publish-diagnostics uri)))]
            [(equal? method "textDocument/didSave")
             (publish-diagnostics (get (get params "textDocument") "uri"))]
            [(equal? method "textDocument/didClose")
             (hashtable-delete! documents (get (get params "textDocument") "uri"))]
            [(equal? method "textDocument/hover") (hover msg params)]
            [(equal? method "textDocument/definition") (definition msg params)]
            [(equal? method "textDocument/documentSymbol") (document-symbols msg params)]
            [(equal? method "shutdown") (respond msg 'null)]
            [(equal? method "exit") (exit 0)]
            [(get msg "id") (send `(("jsonrpc" . "2.0") ("id" . ,(get msg "id"))
                                    ("error" . (("code" . -32601) ("message" . "metodo non supportato")))))])
          (loop))))))
