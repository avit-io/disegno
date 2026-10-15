;; Piano: main si valuta (in modo puro) in un dato, un albero di costruttori di Obj, che qui
;; diventa GraphQL. Il costruttore Tipo.campo-kebab è il campo tipoCampo; i nomi dei suoi
;; binder espliciti sono gli argomenti; per i metodi il primo argomento (self) è l'oggetto.
;; Gli argomenti oggetto si passano per ID: `resolve` riceve la loro catena e restituisce
;; l'ID (dal vivo) o un segnaposto (a secco).
;; branch è l'unico punto in cui il motore decide: `observe` riceve la catena della condizione
;; e restituisce l'esito. Entrambi i rami stanno nel piano; a runtime se ne sceglie solo uno.

(define observe (make-parameter (lambda (ch) (oops "branch richiede una sessione Dagger"))))

;; Host ed Export relativi si risolvono rispetto alla cartella del programma, non a quella corrente.
(define program-dir (make-parameter ""))

(define (explicit sp) (map car (filter (lambda (a) (eq? (cdr a) 'e)) sp)))

(define (map-ltr f xs ys)                                ; map con ordine garantito, da sinistra
  (reverse (fold-left (lambda (acc x y) (cons (f x y) acc)) '() xs ys)))

(define (split-dots s)
  (let loop ([cs (string->list s)] [cur '()] [acc '()])
    (cond [(null? cs) (reverse (cons (list->string (reverse cur)) acc))]
          [(char=? (car cs) #\.) (loop (cdr cs) '() (cons (list->string (reverse cur)) acc))]
          [else (loop (cdr cs) (cons (car cs) cur) acc)])))

(define (camel s)                                        ; with-new-file → withNewFile (come in gen.ss)
  (let loop ([cs (string->list s)] [up #f])
    (cond [(null? cs) ""]
          [(char=? (car cs) #\-) (loop (cdr cs) #t)]
          [else (string-append (string (if up (char-upcase (car cs)) (car cs))) (loop (cdr cs) #f))])))

(define (node v)                                         ; → nome del costruttore se v è un nodo del piano
  (and (eq? (car v) 'vglob)
       (let ([g (gget (cadr v))]) (and g (eq? (g-kind g) 'con) (eq? (g-info g) 'Obj) (cadr v)))))

(define (arg-names c)                                    ; binder espliciti del costruttore
  (let loop ([t (force (g-type (gget c)))] [l 0])
    (if (eq? (car t) 'vpi)
        (let ([rest (loop (force (pi-cod t (vvar l))) (+ l 1))])
          (if (eq? (caddr t) 'e) (cons (cadr t) rest) rest))
        '())))

(define (pick v resolve)                                 ; risolve i branch in testa a v
  (let ([v (force v)])
    (if (eq? (node v) 'branch)
        (let ([xs (explicit (caddr v))])
          (pick (if ((observe) (chain (car xs) resolve)) (cadr xs) (caddr xs)) resolve))
        v)))

;; Dove sta nel sorgente ogni passo della catena (un with-exec che il checker ha marcato con at).
(define step-pos (make-eq-hashtable))
(define (located v ch)
  (when (= (length v) 4) (hashtable-set! step-pos (list-ref ch (- (length ch) 1)) (cadddr v)))
  ch)

(define (chain v resolve)
  (let* ([v (pick v resolve)] [c (node v)])
    (unless c (oops "piano non statico: ~s" (sexp '() (reify 0 v))))
    (let ([args (explicit (caddr v))] [names (arg-names c)])
      (define (field f names args . fixed)
        (cons f (append (map-ltr (lambda (n a) (list n (gql-arg a resolve))) names args) fixed)))
      (define (method f . fixed)                        ; let*: le richieste partono da sinistra a destra
        (let* ([recv (chain (car args) resolve)])
          (append recv (list (apply field f (cdr names) (cdr args) fixed)))))
      (located v
        (case c
          [(%host-dir) (list '(host) (field 'directory names args))]
          [(try-exec) (method 'withExec '(expect ANY))]
          [(cache-volume) (list (field 'cacheVolume names args))]
          [(passes?) (method 'exitCode)]
          [(overlay replace publish) (oops "un'uscita (Export) può stare solo in cima al piano")]
          [else (let ([segs (split-dots (symbol->string c))])
                  (if (string=? (car segs) "Query")
                      (list (field (string->symbol (camel (cadr segs))) names args))
                      (method (string->symbol (camel (cadr segs))))))])))))

(define (gql-arg v resolve)                              ; stringa, naturale, booleano, lista o oggetto (per ID)
  (let ([v (pick v resolve)])
    (cond [(node v) (resolve (chain v resolve))]
          [(eq? (car v) 'vnum) (cadr v)]
          [(eq? (car v) 'vstr) (cadr v)]
          [(and (eq? (car v) 'vglob) (memq (cadr v) '(true false))) (eq? (cadr v) 'true)]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) 'zero)) 0]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) 'add1)) (+ 1 (gql-arg (car (explicit (caddr v))) resolve))]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) 'vuota)) '()]
          [(and (eq? (car v) 'vglob) (eq? (cadr v) '::))
           (let* ([xs (explicit (caddr v))] [x (gql-arg (car xs) resolve)]) (cons x (gql-arg (cadr xs) resolve)))]
          [(and (eq? (car v) 'vglob) (memq (cadr v) '(root /))) (abs-string v resolve)]
          ;; un valore raffinato (Image, Segment, Arg…) va al motore con il suo primo campo
          [(and (eq? (car v) 'vglob) (eq? (g-kind (gget (cadr v))) 'con) (pair? (explicit (caddr v))))
           (gql-arg (car (explicit (caddr v))) resolve)]
          [else (oops "argomento non statico: ~s" (sexp '() (reify 0 v)))])))

(define (abs-string v resolve)                           ; (/ (/ root "go") "pkg") → "/go/pkg"
  (let loop ([v (force v)] [acc '()])
    (cond [(eq? (cadr v) 'root) (if (null? acc) "/" (apply string-append (map (lambda (s) (string-append "/" s)) acc)))]
          [(eq? (cadr v) '/) (let ([xs (explicit (caddr v))]) (loop (force (car xs)) (cons (gql-arg (cadr xs) resolve) acc)))]
          [else (oops "percorso non statico: ~s" (sexp '() (reify 0 v)))])))

;; main : (→ [x (Host "p")] ... (Export Dir)) → catena che termina con export.
(define (plan resolve . entry)
  (let* ([main (if (null? entry) 'main (car entry))]
         [sig (or (hashtable-ref sigs main #f) (oops "manca ~a" main))]
         [hosts (let loop ([t sig])
                  (if (eq? (car t) 'pi)
                      (let ([dom (cadddr t)])
                        (unless (and (eq? (caddr t) 'e) (eq? (car dom) 'app) (equal? (cadr dom) '(glob Host)) (eq? (car (caddr dom)) 'str))
                          (oops "gli argomenti di main devono essere (Host \"percorso\")"))
                        (cons (list 'vglob '%host-dir (list (cons (list 'vstr (in-dir (program-dir) (cadr (caddr dom)))) 'e)))
                              (loop (list-ref t 4))))
                      '()))]
         [v (pick (vapp-sp (ev '() `(glob ,main)) (map (lambda (h) (cons h 'e)) hosts)) resolve)])
    (case (node v)
      [(overlay replace)                                 ; export sull'host; replace è con wipe
       (let* ([path (in-dir (program-dir) (gql-arg (car (explicit (caddr v))) resolve))]
              [dir (chain (cadr (explicit (caddr v))) resolve)])
         (append dir (list `(export (path ,path) (wipe ,(eq? (node v) 'replace))))))]
      [(publish)                                         ; pubblicazione dell'immagine su un registry
       (let* ([ctr (chain (car (explicit (caddr v))) resolve)])
         (append ctr (list `(publish (address ,(gql-arg (cadr (explicit (caddr v))) resolve))))))]
      [else (oops "~a deve restituire un Export" main)])))

;; --- esecuzione ---

;; --- i log: con DISEGNO_LOGS, l'output di ogni with-exec, un gruppo per passo ---
;; Dagger è pigro e ha la cache: chiedere l'output del prefisso che termina con un withExec esegue
;; la catena fino a lì, e la richiesta finale non rifà niente. I log escono nell'ordine dei passi.
;; combinedOutput intreccia stdout e stderr nell'ordine in cui il motore li riceve.
;; ponytail: un passo fallito li ha separati (stdout, poi stderr): intrecciarli vorrebbe dire
;; rieseguire il comando con expect: ANY, che il motore non ha in cache.

(define logged '())                                      ; prefissi già mostrati

(define (log-steps ch)
  (when (getenv "DISEGNO_LOGS")
    (for-each (lambda (i)
                (let ([pre (list-head ch i)])
                  (when (and (eq? (car (list-ref ch (- i 1))) 'withExec) (not (member pre logged)))
                    (set! logged (cons pre logged))
                    (show-step pre))))
              (cdr (iota (+ (length ch) 1))))))

(define (show-args args)                                ; il comando, con le virgolette dove servono
  (format "~{~a~^ ~}" (map (lambda (a) (if (memv #\space (string->list a)) (format "~s" a) a)) args)))

(define (lines . ss)                                     ; testi uno dopo l'altro, ciascuno chiuso da un a capo
  (apply string-append (map (lambda (s) (if (or (string=? s "") (char=? (string-ref s (- (string-length s) 1)) #\newline)) s (string-append s "\n"))) ss)))

(define (show-step pre)
  (let* ([step (list-ref pre (- (length pre) 1))] [title (show-args (cadr (assq 'args (cdr step))))])
    (guard (e [(exec-error e)
               => (lambda (x)                            ; il motore dà stdout e stderr separati
                    (define (ext k) (cond [(assoc k x) => cdr] [else ""]))
                    (log-group title (lines (ext "stdout") (ext "stderr")) #t)
                    (step-failed (hashtable-ref step-pos step #f) (ext "exitCode") title))])
      (log-group title (lines (submit-leaf (append pre '((combinedOutput)))))))))

;; Un passo fallito: dove sta nel sorgente, con che exit code, quale comando. Su GitHub anche
;; un'annotazione, che compare sul file e sulla riga.
(define (step-failed pos code title)
  (let ([what (format "passo fallito (exit ~a): ~a" code title)] [at (and pos (vector->list pos))])
    (when (getenv "GITHUB_ACTIONS")
      (printf "::error~@[ ~{file=~a,line=~a,col=~a~}~]::~a\n" at what))
    (error 'disegno (format "~@[~{~a:~a:~a~}: ~]~a" at what))))

(define (log-group title body . failed)                 ; un passo fallito resta aperto, dove si può
  (cond [(getenv "GITHUB_ACTIONS") (printf "::group::~a\n~a::endgroup::\n" title body)]
        [(getenv "GITLAB_CI")
         (let ([id (format "passo-~a" (length logged))] [t (time-second (current-time))])
           (printf "\x1b;[0Ksection_start:~a:~a[collapsed=~a]\r\x1b;[0K~a\n~a\x1b;[0Ksection_end:~a:~a\r\x1b;[0K\n"
                   t id (if (null? failed) "true" "false") title body t id))]
        [else (printf "── ~a\n~a" title body)])
  (flush-output-port))

(define (resolve-live ch) (log-steps ch) (submit-leaf (append ch '((id)))))
(define (resolve-dry ch) (format "<~a>" (plan->graphql ch)))

;; ponytail: un'osservazione booleana è un Boolean GraphQL o un exit code (vero se 0).
(define (observe-live ch)
  (log-steps ch)
  (let ([r (submit-leaf ch)])
    (cond [(boolean? r) r] [(number? r) (= r 0)] [else (oops "osservazione non booleana: ~s" r)])))

(define (run entry)
  (parameterize ([observe observe-live])
    (guard (e [(exec-error e) => (lambda (x)                ; anche senza log: quale passo, e dove
                                   (let ([cmd (cdr (assoc "cmd" x))])
                                     (step-failed (cmd-pos cmd) (cdr (assoc "exitCode" x)) (show-args cmd))))])
      (let ([p (plan resolve-live entry)]) (log-steps p) (submit-leaf p)))))

(define (exec-error e)                                   ; → le extensions di un EXEC_ERROR, o #f
  (and (irritants-condition? e) (pair? (condition-irritants e))
       (let ([x (car (condition-irritants e))])
         (and (list? x) (equal? (cond [(assoc "_type" x) => cdr] [else #f]) "EXEC_ERROR") x))))

;; ponytail: il passo si ritrova dal comando; due with-exec identici danno la posizione di uno dei due.
(define (cmd-pos cmd)
  (let-values ([(steps poss) (hashtable-entries step-pos)])
    (let loop ([i 0])
      (cond [(= i (vector-length steps)) #f]
            [(equal? (cond [(assq 'args (cdr (vector-ref steps i))) => cadr] [else #f]) cmd) (vector-ref poss i)]
            [else (loop (+ i 1))]))))

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
