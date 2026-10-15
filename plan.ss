;; Piano: main si valuta (in modo puro) in un albero di extern, che qui diventa GraphQL.
;; Gli argomenti oggetto (una Dir passata a withDirectory) si passano per ID: `resolve`
;; riceve la loro catena e restituisce l'ID (dal vivo) o un segnaposto (a secco).
;; branch è l'unico punto in cui il motore decide: `observe` riceve la catena della condizione
;; e restituisce l'esito. Entrambi i rami sono già noti; a runtime se ne sceglie solo uno.

(define observe (make-parameter (lambda (ch) (oops "branch richiede una sessione Dagger"))))

(define (explicit sp) (map car (filter (lambda (a) (eq? (cdr a) 'e)) sp)))

(define (split-dots s)
  (let loop ([cs (string->list s)] [cur '()] [acc '()])
    (cond [(null? cs) (reverse (cons (list->string (reverse cur)) acc))]
          [(char=? (car cs) #\.) (loop (cdr cs) '() (cons (list->string (reverse cur)) acc))]
          [else (loop (cdr cs) (cons (car cs) cur) acc)])))

(define (extern-of v)                                    ; → g se v è un extern applicato, altrimenti #f
  (let ([g (and (eq? (car v) 'vglob) (gget (cadr v)))]) (and g (eq? (g-kind g) 'extern) g)))

(define (pick v resolve)                                 ; risolve i branch in testa a v
  (let* ([v (force v)] [g (extern-of v)])
    (if (and g (eq? (car (car (g-info g))) '%branch))
        (let ([xs (explicit (caddr v))])
          (pick (if ((observe) (chain (car xs) resolve)) (cadr xs) (caddr xs)) resolve))
        v)))

(define (chain v resolve)
  (let* ([v (pick v resolve)] [g (extern-of v)])
    (unless g (oops "piano non statico: ~s" (sexp '() (reify 0 v))))
    (let* ([spec (car (g-info g))] [field (symbol->string (car spec))] [names (cdr (g-info g))]
           [args (explicit (caddr v))] [segs (split-dots field)])
      (unless (= (length args) (length names)) (oops "~a non è applicato del tutto" (cadr v)))
      (if (char-upper-case? (string-ref field 0))  ; Tipo.campo: metodo sul primo argomento
          (let* ([recv (chain (car args) resolve)])      ; let*: le richieste partono da sinistra a destra
            (append recv (list (call-field (cadr segs) (cdr names) (cdr args) (cdr spec) resolve))))
          (append (map (lambda (s) (list (string->symbol s))) (list-head segs (- (length segs) 1)))
                  (list (call-field (list-ref segs (- (length segs) 1)) names args (cdr spec) resolve)))))))

(define (call-field name names args fixed resolve)
  (cons (string->symbol name) (append (map-ltr (lambda (n a) (list n (gql-arg a resolve))) names args) fixed)))

(define (map-ltr f xs ys)                                ; map con ordine garantito, da sinistra
  (reverse (fold-left (lambda (acc x y) (cons (f x y) acc)) '() xs ys)))

(define (gql-arg v resolve)                              ; stringa, naturale, booleano, lista o oggetto (per ID)
  (let ([v (pick v resolve)])
    (cond [(eq? (car v) 'vstr) (cadr v)]
          [(and (eq? (car v) 'vglob) (memq (cadr v) '(true false))) (eq? (cadr v) 'true)]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) 'zero)) 0]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) 'add1)) (+ 1 (gql-arg (car (explicit (caddr v))) resolve))]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) 'vuota)) '()]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) '::))
           (let* ([xs (explicit (caddr v))] [x (gql-arg (car xs) resolve)]) (cons x (gql-arg (cadr xs) resolve)))]
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
         [v (pick (vapp-sp (ev '() `(glob ,main)) (map (lambda (h) (cons h 'e)) hosts)) resolve)])
    (unless (and (eq? (car v) 'vglob) (memq (cadr v) '(overlay replace))) (oops "~a deve restituire un Export" main))
    (let* ([path (pick (car (explicit (caddr v))) resolve)]
           [_ (unless (eq? (car path) 'vstr) (oops "il percorso di export deve essere noto"))]
           [dir (chain (cadr (explicit (caddr v))) resolve)])
      (append dir (list `(export (path ,(cadr path)) (wipe ,(eq? (cadr v) 'replace))))))))

;; --- esecuzione ---

(define (resolve-live ch) (submit-leaf (append ch '((id)))))
(define (resolve-dry ch) (format "<~a>" (plan->graphql ch)))

;; ponytail: un'osservazione booleana è un Boolean GraphQL o un exit code (vero se 0).
(define (observe-live ch)
  (let ([r (submit-leaf ch)])
    (cond [(boolean? r) r] [(number? r) (= r 0)] [else (oops "osservazione non booleana: ~s" r)])))

(define (run entry) (parameterize ([observe observe-live]) (submit-leaf (plan resolve-live entry))))

;; A secco: un piano per ogni combinazione di esiti dei branch, in profondità.
;; → lista di ((catena-condizione . esito) ...) . catena
(define (all-plans entry)
  (let explore ([prefix '()])
    (let* ([taken '()]
           [p (parameterize ([observe (lambda (ch)
                                        (let ([b (if (< (length taken) (length prefix)) (list-ref prefix (length taken)) #t)])
                                          (set! taken (append taken (list (cons ch b))))
                                          b))])
                (plan resolve-dry entry))])
      (cons (cons taken p)
            (apply append (map (lambda (i) (explore (append (map cdr (list-head taken i)) '(#f))))
                               (reverse (filter (lambda (i) (>= i (length prefix))) (iota (length taken))))))))))
