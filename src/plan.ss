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

;; Un passo: si apre il gruppo, le righe arrivano dal flusso mentre il passo gira, si chiude.
;; Un passo in cache non esegue niente e il flusso tace: allora si mostra combinedOutput, che
;; intreccia stdout e stderr nell'ordine in cui il motore li ha ricevuti.
;; ponytail: un passo fallito senza flusso ha stdout e stderr separati (le extensions
;; dell'errore): intrecciarli vorrebbe dire rieseguirlo con expect: ANY, fuori dalla cache.
(define (show-step pre)
  (let* ([step (list-ref pre (- (length pre) 1))] [title (show-args (cadr (assq 'args (cdr step))))])
    (start-stream!)
    (set! log-port (current-output-port))
    (group-open title)
    (let ([before streamed] [e0 eofs])
      (guard (e [(exec-error e)
                 => (lambda (x)
                      (define (ext k) (cond [(assoc k x) => cdr] [else ""]))
                      (settle! before e0)
                      (when (= streamed before) (out (lines (ext "stdout") (ext "stderr"))))
                      (group-close)
                      (step-failed (hashtable-ref step-pos step #f) (ext "exitCode") title))])
        (let ([o (submit-leaf (append pre '((combinedOutput))))])
          (settle! before e0)
          (when (= streamed before) (out o))
          (group-close))))))

;; --- il flusso: le righe dei comandi appena il motore le riceve (in CI, con DISEGNO_LOGS) ---

(define out-mutex (make-mutex))                          ; il thread del flusso e il principale
(define log-port #f)                                     ; la porta del passo corrente
(define streamed 0)                                      ; righe arrivate dal flusso
(define eofs 0)                                          ; canali chiusi (stdio.eof): due per comando
(define at-line-start #t)
(define stream-on #f)                                    ; #f: da aprire; un fd: aperto; no: chiuso o assente

(define stream-since 0)                                 ; ns: il flusso ripete lo storico della sessione
(define pending '())                                     ; (istante . testo), in ordine di istante

(define (now-ns) (let ([t (current-time 'time-utc)]) (+ (* (time-second t) 1000000000) (time-nanosecond t))))

(define (start-stream!)
  (unless stream-on
    (set! stream-since (now-ns))
    (set! stream-on (guard (e [#t 'no])
                      (log-stream (string->number (getenv "DAGGER_SESSION_PORT")) (getenv "DAGGER_SESSION_TOKEN") on-log)))
    (when (number? stream-on)
      (let ([fd stream-on])                             ; finché il flusso è questo
        (fork-thread (lambda ()
                       (let loop ()
                         (sleep (make-time 'time-duration 50000000 0))
                         (when (eqv? stream-on fd) (flush! (- (now-ns) window)) (loop)))))))))

;; Il motore manda stdout e stderr a pacchetti separati: una riga di stderr può arrivare 200 ms
;; dopo una di stdout scritta più tardi. Ogni record porta l'istante in cui il comando l'ha
;; scritta: le righe aspettano nel buffer finché sono più vecchie della finestra, poi escono in
;; ordine d'istante.
;; ponytail: finestra fissa di 300 ms e orologio del motore confrontato con quello locale (lo
;; stesso, con un motore locale); con un motore remoto servirebbe la deriva tra i due.
(define window 300000000)

(define (flush! until)                                   ; stampa le righe con istante ≤ until
  (with-mutex out-mutex
    (let loop ()
      (when (and (pair? pending) (<= (caar pending) until))
        (emit (cdar pending))
        (set! pending (cdr pending))
        (loop)))))

(define (insert-pending t s)                             ; in ordine; a parità, nell'ordine d'arrivo
  (let loop ([ps pending])
    (cond [(or (null? ps) (< t (caar ps))) (cons (cons t s) ps)]
          [else (cons (car ps) (loop (cdr ps)))])))

;; Il flusso si chiude prima della sessione: Dagger non sopporta una richiesta ancora aperta.
(define (stop-stream!)
  (when (number? stream-on) (log-stream-stop stream-on) (set! stream-on #f)))   ; un altro run lo riapre

;; Solo l'output dei comandi (stdio.stream); non i valori restituiti, che il motore ripete come
;; log verbosi (dagger.io/logs.verbose): combinedOutput uscirebbe due volte. E non lo storico:
;; all'iscrizione il motore rimanda i log già prodotti nella sessione.
(define (on-log rec)
  (let ([body (json-field (json-field rec "body" '()) "stringValue" #f)]
        [keys (map (lambda (a) (json-field a "key" #f)) (json-field rec "attributes" '()))]
        [t (or (string->number (json-field rec "timeUnixNano" "0")) 0)])
    (when (and body log-port (member "stdio.stream" keys) (not (member "dagger.io/logs.verbose" keys))
               (>= t stream-since))
      (with-mutex out-mutex
        (if (member "stdio.eof" keys)
            (set! eofs (+ eofs 1))
            (begin (set! streamed (+ streamed 1)) (set! pending (insert-pending t body))))))))

(define (out s) (with-mutex out-mutex (emit s)))
(define (emit s)
  (unless (string=? s "")
    (display s log-port) (flush-output-port log-port)
    (set! at-line-start (char=? (string-ref s (- (string-length s) 1)) #\newline))))

;; Le ultime righe possono arrivare dopo la risposta: si aspetta che il comando chiuda i canali.
(define (settle! s0 e0)                                  ; s0, e0: righe e eof a inizio passo
  (when (number? stream-on)
    (let loop ([k 0])
      (sleep (make-time 'time-duration 50000000 0))
      (unless (or (>= (- eofs e0) 2)                     ; stdout e stderr chiusi: il comando ha finito
                  (and (>= k 2) (= streamed s0) (= eofs e0))   ; niente di niente: in cache
                  (> k 40))                             ; ponytail: 2 s, poi si chiude comunque
        (loop (+ k 1))))
    (flush! +inf.0)))                                     ; il passo è finito: tutto il buffer

(define (gitlab-section what)                            ; section_start / section_end del passo
  (format "\x1b;[0Ksection_~a:~a:passo-~a" what (time-second (current-time)) (length logged)))

;; ponytail: su GitLab le sezioni partono chiuse anche per il passo fallito: si apre prima di
;; sapere come finisce. Il messaggio d'errore, fuori dalla sezione, dice comunque dove guardare.
(define (group-open title)
  (out (cond [(getenv "GITHUB_ACTIONS") (format "::group::~a\n" title)]
             [(getenv "GITLAB_CI") (format "~a[collapsed=true]\r\x1b;[0K~a\n" (gitlab-section "start") title)]
             [else (format "── ~a\n" title)])))

(define (group-close)
  (unless at-line-start (out "\n"))
  (out (cond [(getenv "GITHUB_ACTIONS") "::endgroup::\n"]
             [(getenv "GITLAB_CI") (format "~a\r\x1b;[0K\n" (gitlab-section "end"))]
             [else ""])))

;; Un passo fallito: dove sta nel sorgente, con che exit code, quale comando. Su GitHub anche
;; un'annotazione, che compare sul file e sulla riga.
(define (step-failed pos code title)
  (let ([what (format "passo fallito (exit ~a): ~a" code title)] [at (and pos (vector->list pos))])
    (when (getenv "GITHUB_ACTIONS")
      (printf "::error~@[ ~{file=~a,line=~a,col=~a~}~]::~a\n" at what))
    (error 'disegno (format "~@[~{~a:~a:~a~}: ~]~a" at what))))

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
      (dynamic-wind void
        (lambda () (let ([p (plan resolve-live entry)]) (log-steps p) (submit-leaf p)))
        stop-stream!))))

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
