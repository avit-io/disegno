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

;; The checker's lines: "file:line:col: message" opens a diagnostic, an unlocated line continues
;; the previous one (the context and goal of a TODO). Only this file's diagnostics are kept.
(define (diagnostics text tmp stderr)
  (let loop ([ls (lines stderr)] [acc '()] [open? #f])
    (cond [(null? ls) (reverse acc)]
          [(parse-location (car ls))
           => (lambda (e) (if (string=? (car e) tmp)
                              (loop (cdr ls) (cons (cdr e) acc) #t)
                              (loop (cdr ls) acc #f)))]
          [(and open? (pair? acc))
           (let ([d (car acc)]) (loop (cdr ls) (cons (list (car d) (cadr d) (string-append (caddr d) "\n" (car ls))) (cdr acc)) #t))]
          [else (loop (cdr ls) acc open?)])))

(define (todo? msg) (and (>= (string-length msg) 4) (string=? (substring msg 0 4) "TODO")))

(define (publish-diagnostics uri)
  (let* ([text (hashtable-ref documents uri "")] [r (run-on text "check")]
         [ds (diagnostics text (car r) (caddr r))])
    (send `(("jsonrpc" . "2.0") ("method" . "textDocument/publishDiagnostics")
            ("params" . (("uri" . ,uri)
                         ("diagnostics" . ,(list->vector
                                             (let loop ([ds ds] [seen '()] [out '()])   ; seen: positions of earlier TODOs
                                               (if (null? ds)
                                                   (reverse out)
                                                   (let* ([d (car ds)] [line (- (car d) 1)] [col (- (cadr d) 1)] [msg (caddr d)]
                                                          [nth (length (filter (lambda (p) (equal? p (cons line col))) seen))])
                                                     (loop (cdr ds) (if (todo? msg) (cons (cons line col) seen) seen)
                                                           (cons `(("range" . ,(diagnostic-range text line col msg nth))
                                                                   ("severity" . ,(if (todo? msg) 3 1)) ("source" . "disegno") ("message" . ,msg))
                                                                 out)))))))))))))

;; The checker knows the position of the nearest form, not of an atom: an unknown name is
;; searched from there (or, if not after it, before it), the n-th TODO of a form is its n-th TODO token; otherwise the word at
;; the position, or the form up to the end of its line.
(define (diagnostic-range text line col msg nth)
  (let* ([from (offset-of text line col)]
         [token (cond [(todo? msg) "TODO"]
                      [(prefix? "nome sconosciuto: " msg)
                       (let ([rest (substring msg 18 (string-length msg))])
                         (car (split-on (car (split-on rest #\newline)) #\,)))]
                      [else #f])]
         [at (and token (or (find-token text token from nth) (find-token-before text token from)))])
    (if at
        (offsets->range text at (+ at (string-length token)))
        (let* ([n (string-length text)]
               [end (if (and (< from n) (char=? (string-ref text from) #\())
                        (form-end text from)
                        (let loop ([j from]) (if (and (< j n) (not (delim? (string-ref text j)))) (loop (+ j 1)) j)))])
          (offsets->range text from (max end (min n (+ from 1))))))))

(define (prefix? p s) (and (>= (string-length s) (string-length p)) (string=? (substring s 0 (string-length p)) p)))

(define (delim? c) (or (char-whitespace? c) (memv c '(#\( #\) #\[ #\] #\{ #\} #\; #\, #\"))))

(define (offset-of text line col)                        ; (line, col) from 0 → offset
  (let loop ([i 0] [l 0])
    (cond [(= l line) (min (+ i col) (string-length text))]
          [(>= i (string-length text)) i]
          [else (loop (+ i 1) (if (char=? (string-ref text i) #\newline) (+ l 1) l))])))

(define (line-col text off)                              ; offset → (line . col), from 0
  (let loop ([i 0] [l 0] [c 0])
    (if (or (>= i off) (>= i (string-length text))) (cons l c)
        (if (char=? (string-ref text i) #\newline) (loop (+ i 1) (+ l 1) 0) (loop (+ i 1) l (+ c 1))))))

(define (offsets->range text a b)
  (let ([s (line-col text a)] [e (line-col text b)])
    `(("start" . ,(position (car s) (cdr s))) ("end" . ,(position (car e) (cdr e))))))

(define (find-token text tok from nth)                   ; offset of the nth whole occurrence of tok after from, or #f
  (let ([n (string-length text)] [k (string-length tok)])
    (let loop ([i from] [nth nth])
      (cond [(> (+ i k) n) #f]
            [(and (string=? (substring text i (+ i k)) tok)
                  (or (= i 0) (delim? (string-ref text (- i 1))))
                  (or (= (+ i k) n) (delim? (string-ref text (+ i k)))))
             (if (zero? nth) i (loop (+ i k) (- nth 1)))]
            [else (loop (+ i 1) nth)]))))

(define (form-end text from)                             ; the closing paren of the form at from, at most the end of its line
  (let ([n (string-length text)])
    (let loop ([j from] [depth 0])
      (cond [(or (>= j n) (char=? (string-ref text j) #\newline)) j]
            [(char=? (string-ref text j) #\() (loop (+ j 1) (+ depth 1))]
            [(char=? (string-ref text j) #\)) (if (= depth 1) (+ j 1) (loop (+ j 1) (- depth 1)))]
            [else (loop (+ j 1) depth)]))))

(define (find-token-before text tok to)                  ; offset of the last whole occurrence of tok before to, or #f
  (let loop ([i (find-token text tok 0 0)] [last #f])
    (if (and i (< i to)) (loop (find-token text tok (+ i 1) 0) i) last)))

;; --- il nome sotto il cursore ---

(define (word-at text line character)                    ; il simbolo che contiene la posizione, o #f
  (let* ([lines (split-on text #\newline)]
         [s (and (< line (length lines)) (list-ref lines line))])
    (and s
         (let* ([n (string-length s)] [i (min character n)]
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

(define symbol-kinds '((claim . 12) (data . 10) (record . 23) (extern . 12)))   ; Function, Enum, Struct

(define (document-symbols msg params)
  (let*-values ([(text) (hashtable-ref documents (get (get params "textDocument") "uri") "")] [(t) text])
    (let* ([sfd (make-source-file-descriptor "doc" (open-bytevector-input-port (string->utf8 t)))]
           [p (open-string-input-port t)]
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
                                 [r (offsets->range text (source-object-bfp (annotation-source a)) (source-object-efp (annotation-source a)))])
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
