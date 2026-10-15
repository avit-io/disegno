;; Piano: main si valuta (in modo puro) in un albero di extern, che qui diventa GraphQL.
;; Gli argomenti oggetto (una Dir passata a withDirectory) si passano per ID: `resolve`
;; riceve la loro catena e restituisce l'ID (dal vivo) o un segnaposto (a secco).

(define (explicit sp) (map car (filter (lambda (a) (eq? (cdr a) 'e)) sp)))

(define (split-dots s)
  (let loop ([cs (string->list s)] [cur '()] [acc '()])
    (cond [(null? cs) (reverse (cons (list->string (reverse cur)) acc))]
          [(char=? (car cs) #\.) (loop (cdr cs) '() (cons (list->string (reverse cur)) acc))]
          [else (loop (cdr cs) (cons (car cs) cur) acc)])))

(define (chain v resolve)
  (let* ([v (force v)] [g (and (eq? (car v) 'vglob) (gget (cadr v)))])
    (unless (and g (eq? (g-kind g) 'extern)) (oops "piano non statico: ~s" (sexp '() (reify 0 v))))
    (let* ([field (symbol->string (car (g-info g)))] [names (cdr (g-info g))]
           [args (explicit (caddr v))] [segs (split-dots field)])
      (unless (= (length args) (length names)) (oops "~a non è applicato del tutto" (cadr v)))
      (if (char-upper-case? (string-ref field 0))  ; Tipo.campo: metodo sul primo argomento
          (append (chain (car args) resolve) (list (call-field (cadr segs) (cdr names) (cdr args) resolve)))
          (append (map (lambda (s) (list (string->symbol s))) (list-head segs (- (length segs) 1)))
                  (list (call-field (list-ref segs (- (length segs) 1)) names args resolve)))))))

(define (call-field name names args resolve)
  (cons (string->symbol name) (map (lambda (n a) (list n (gql-arg a resolve))) names args)))

(define (gql-arg v resolve)                              ; stringa, lista o oggetto (per ID)
  (let ([v (force v)])
    (cond [(eq? (car v) 'vstr) (cadr v)]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) 'vuota)) '()]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) '::))
           (let ([xs (explicit (caddr v))]) (cons (gql-arg (car xs) resolve) (gql-arg (cadr xs) resolve)))]
          [else (resolve (chain v resolve))])))

;; main : (→ [x (Host "p")] ... (Export Dir)) → catena che termina con export.
(define (plan resolve . entry)
  (let* ([main (if (null? entry) 'main (car entry))]
         [sig (or (hashtable-ref sigs main #f) (oops "manca ~a" main))]
         [hosts (let loop ([t sig])
                  (if (eq? (car t) 'pi)
                      (let ([dom (cadddr t)])
                        (unless (and (eq? (caddr t) 'e) (eq? (car dom) 'app) (equal? (cadr dom) '(glob Host)) (eq? (car (caddr dom)) 'str))
                          (oops "gli argomenti di main devono essere (Host \"percorso\")"))
                        (cons `(vglob %host-dir ((,(ev '() (caddr dom)) . e))) (loop (list-ref t 4))))
                      '()))]
         [v (force (vapp-sp (ev '() `(glob ,main)) (map (lambda (h) (cons h 'e)) hosts)))])
    (unless (and (eq? (car v) 'vglob) (memq (cadr v) '(overlay replace))) (oops "main deve restituire un Export"))
    (let ([path (force (car (explicit (caddr v))))])
      (unless (eq? (car path) 'vstr) (oops "il percorso di export deve essere noto"))
      (append (chain (cadr (explicit (caddr v))) resolve)
              (list `(export (path ,(cadr path)) (wipe ,(eq? (cadr v) 'replace))))))))
