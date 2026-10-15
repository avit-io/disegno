;; Il server LSP: disegno lsp. JSON-RPC su stdin/stdout, con le intestazioni Content-Length.
;; Diagnostica all'apertura e al salvataggio: il testo del documento si controlla in un processo
;; a sé (disegno check), così ogni controllo parte pulito; l'errore file:riga:colonna: messaggio
;; diventa una diagnostica. Si legge e si scrive in byte: Content-Length conta byte, non caratteri.
;; Hover: il tipo del nome globale sotto il cursore (disegno type).
;; ponytail: solo il primo errore del file, e solo all'apertura e al salvataggio; hover sulle variabili locali e
;; diagnostica mentre si scrive verranno se servono.

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

;; --- diagnostica ---

(define documents (make-hashtable string-hash string=?))  ; uri → testo

(define (uri->path uri) (if (and (> (string-length uri) 7) (string=? (substring uri 0 7) "file://")) (substring uri 7 (string-length uri)) uri))

(define scheme-bin (or (getenv "DISEGNO_SCHEME") "scheme"))

;; Controlla il testo in un processo a sé; → #f, o (riga colonna messaggio) del primo errore.
(define (check-document uri text)
  (let* ([dir (path-parent (uri->path uri))]
         [tmp (format "/tmp/disegno-lsp-~a.disegno" (random 1000000000))]
         [errf (string-append tmp ".err")])
    (call-with-output-file tmp (lambda (p) (put-string p text)) 'replace)
    (system (format "~a --script ~a check ~a >/dev/null 2>~a" scheme-bin (at-root "src/main.ss") tmp errf))
    (let ([err (call-with-input-file errf get-string-all)])
      (delete-file tmp) (delete-file errf)
      (parse-error tmp (if (eof-object? err) "" err)))))

(define (parse-error file err)                           ; "file:riga:colonna: messaggio" → (riga colonna messaggio)
  (let ([k (string-length file)])
    (and (> (string-length err) k) (string=? (substring err 0 k) file)
         (let* ([rest (substring err (+ k 1) (string-length err))] [parts (split-on rest #\:)])
           (and (>= (length parts) 3) (string->number (car parts)) (string->number (cadr parts))
                (list (string->number (car parts)) (string->number (cadr parts))
                      (string-trim (let ([m (substring rest (+ 2 (string-length (car parts)) (string-length (cadr parts))) (string-length rest))])
                                     (let ([nl (memv #\newline (string->list m))]) (if nl (substring m 0 (- (string-length m) (length nl))) m))))))))))

(define (publish-diagnostics uri)
  (let* ([r (check-document uri (hashtable-ref documents uri ""))]
         [diags (if r
                    (let ([line (- (car r) 1)] [col (- (cadr r) 1)])
                      (vector `(("range" . (("start" . (("line" . ,line) ("character" . ,col)))
                                            ("end" . (("line" . ,line) ("character" . ,(+ col 1))))))
                                ("severity" . 1) ("source" . "disegno") ("message" . ,(caddr r)))))
                    (vector))])
    (send `(("jsonrpc" . "2.0") ("method" . "textDocument/publishDiagnostics")
            ("params" . (("uri" . ,uri) ("diagnostics" . ,diags)))))))

;; --- hover: il tipo del nome sotto il cursore (disegno type, in un processo a sé) ---

(define (word-at text line character)                    ; il simbolo che contiene la posizione, o #f
  (let* ([lines (split-on text #\newline)]
         [s (and (< line (length lines)) (list-ref lines line))])
    (and s
         (let* ([delim? (lambda (c) (or (char-whitespace? c) (memv c '(#\( #\) #\[ #\] #\; #\, #\"))))]
                [n (string-length s)] [i (min character n)]
                [start (let loop ([j i]) (if (and (> j 0) (not (delim? (string-ref s (- j 1))))) (loop (- j 1)) j))]
                [end (let loop ([j i]) (if (and (< j n) (not (delim? (string-ref s j)))) (loop (+ j 1)) j))])
           (and (< start end) (substring s start end))))))

(define (type-at uri text word)                          ; → testo dei tipi, o #f
  (let* ([tmp (format "/tmp/disegno-lsp-~a.disegno" (random 1000000000))] [out (string-append tmp ".out")])
    (call-with-output-file tmp (lambda (p) (put-string p text)) 'replace)
    (let* ([ok (zero? (system (format "~a --script ~a type ~a '~a' >~a 2>/dev/null" scheme-bin (at-root "src/main.ss") tmp word out)))]   ; let*: prima il comando
          [r (call-with-input-file out get-string-all)])
      (delete-file tmp) (when (file-exists? out) (delete-file out))
      (and ok (string? r) r))))

(define (hover msg params)
  (let* ([uri (get (get params "textDocument") "uri")] [pos (get params "position")]
         [text (hashtable-ref documents uri "")]
         [word (word-at text (get pos "line") (get pos "character"))]
         [types (and word (not (memv #\' (string->list word))) (type-at uri text word))])
    (respond msg (if types
                     `(("contents" . (("kind" . "markdown") ("value" . ,(string-append "```disegno\n" types "```")))))
                     'null))))

;; --- il ciclo ---

(define (serve)
  (let loop ()
    (let ([msg (read-message)])
      (when msg
        (let ([method (get msg "method")] [params (get msg "params")])
          (cond
            [(equal? method "initialize")
             (respond msg `(("capabilities" . (("textDocumentSync" . (("openClose" . #t) ("change" . 1) ("save" . #t)))
                                               ("hoverProvider" . #t)))
                            ("serverInfo" . (("name" . "disegno")))))]
            [(member method '("textDocument/didOpen"))
             (let ([doc (get params "textDocument")])
               (hashtable-set! documents (get doc "uri") (get doc "text"))
               (publish-diagnostics (get doc "uri")))]
            [(equal? method "textDocument/didChange")
             (let ([changes (get params "contentChanges")])
               (when (pair? changes)
                 (hashtable-set! documents (get (get params "textDocument") "uri") (get (car (last-pair changes)) "text"))))]
            [(equal? method "textDocument/didSave")
             (publish-diagnostics (get (get params "textDocument") "uri"))]
            [(equal? method "textDocument/didClose")
             (hashtable-delete! documents (get (get params "textDocument") "uri"))]
            [(equal? method "textDocument/hover") (hover msg params)]
            [(equal? method "shutdown") (respond msg 'null)]
            [(equal? method "exit") (exit 0)]
            [(get msg "id") (send `(("jsonrpc" . "2.0") ("id" . ,(get msg "id"))
                                    ("error" . (("code" . -32601) ("message" . "metodo non supportato")))))])
          (loop))))))
