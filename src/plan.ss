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
       (let ([g (gget (cadr v))]) (and g (eq? (g-kind g) 'con) (bi? (g-info g) 'obj) (cadr v)))))

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

;; Di ogni passo della catena si ricorda: dove sta nel sorgente e a quale voce appartiene (un
;; with-exec marcato dal checker), e se è lavoro, cioè dipende da un input del programma (un
;; Host), o preparazione dell'ambiente.
(define step-pos (make-eq-hashtable))
(define step-voce (make-eq-hashtable))
(define step-work (make-eq-hashtable))
(define (located v ch)
  (let ([last (list-ref ch (- (length ch) 1))])
    (cond [(v-pos v) => (lambda (p) (hashtable-set! step-pos last p))])
    (hashtable-set! step-work last (on-input? v))
    (cond [(v-name v) => (lambda (n) (hashtable-set! step-voce last n))]))
  ch)

(define input-memo (make-eq-hashtable))
(define (on-input? v)                                    ; il valore dipende da un Host?
  (let ([v (force v)])
    (and (eq? (car v) 'vglob)
         (or (eq? (cadr v) '%host-dir)
             (let ([m (hashtable-ref input-memo v '?)])
               (if (eq? m '?)
                   (let ([r (exists (lambda (a) (on-input? (car a))) (caddr v))]) (hashtable-set! input-memo v r) r)
                   m))))))

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
          [(and (eq? (car v) 'vglob) (or (bi? (cadr v) 'true) (bi? (cadr v) 'false))) (bi? (cadr v) 'true)]
          [(and (eq? (car v) 'vglob) (bi? (cadr v) 'zero)) 0]
          [(and (eq? (car v) 'vglob) (bi? (cadr v) 'suc)) (+ 1 (gql-arg (car (explicit (caddr v))) resolve))]
          [(and (eq? (car v) 'vglob) (bi? (cadr v) 'nil)) '()]
          [(and (eq? (car v) 'vglob) (bi? (cadr v) 'cons))
           (let* ([xs (explicit (caddr v))] [x (gql-arg (car xs) resolve)]) (cons x (gql-arg (cadr xs) resolve)))]
          [(and (eq? (car v) 'vglob) (or (bi? (cadr v) 'root) (bi? (cadr v) 'slash))) (abs-string v resolve)]
          ;; un valore raffinato (Image, Segment, Arg…) va al motore con il suo primo campo
          [(and (eq? (car v) 'vglob) (eq? (g-kind (gget (cadr v))) 'con) (pair? (explicit (caddr v))))
           (gql-arg (car (explicit (caddr v))) resolve)]
          [else (oops "argomento non statico: ~s" (sexp '() (reify 0 v)))])))

(define (abs-string v resolve)                           ; (/ (/ root "go") "pkg") → "/go/pkg"
  (let loop ([v (force v)] [acc '()])
    (cond [(bi? (cadr v) 'root) (if (null? acc) "/" (apply string-append (map (lambda (s) (string-append "/" s)) acc)))]
          [(bi? (cadr v) 'slash) (let ([xs (explicit (caddr v))]) (loop (force (car xs)) (cons (gql-arg (cadr xs) resolve) acc)))]
          [else (oops "percorso non statico: ~s" (sexp '() (reify 0 v)))])))

;; main : (→ [x (Host "p")] ... (Export Dir)) → catena che termina con export.
(define (plan resolve . entry)
  (let* ([main (if (null? entry) 'main (car entry))]
         [sig (or (hashtable-ref sigs main #f) (oops "manca ~a" main))]
         [hosts (let loop ([t sig])
                  (if (eq? (car t) 'pi)
                      (let ([dom (cadddr t)])
                        (unless (and (eq? (caddr t) 'e) (eq? (car dom) 'app) (equal? (cadr dom) `(glob ,(bi 'host))) (eq? (car (caddr dom)) 'str))
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

;; --- il resoconto: con DISEGNO_LOGS, una riga per voce del programma ---
;; Il log dice ciò che non si sapeva prima di eseguire: com'è andata ogni voce, quanto ha
;; impiegato, che cosa si è osservato. Il piano e le sue proprietà erano già noti. Una voce è una
;; definizione del programma che costruisce un pezzo di piano (chez, test, pubblica); i passi che
;; nessuna definizione ha nominato appartengono al punto d'ingresso. L'output dei comandi è la
;; prova: in CI sta nel gruppo chiuso della voce, altrove si mostra solo se la voce fallisce.
;; Dagger è pigro e ha la cache: chiedere l'output del prefisso che termina con un withExec esegue
;; la catena fino a lì, e la richiesta finale non rifà niente.

(define (env? name)                                      ; definita e non vuota: "" vale come assente
  (let ([v (getenv name)]) (and v (not (string=? v "")))))

(define entry-name (make-parameter 'main))
(define logged '())                                      ; prefissi già eseguiti

(define (last-of l) (list-ref l (- (length l) 1)))
(define (step-args step) (cadr (assq 'args (cdr step))))

(define (log-steps ch)
  (when (env? "DISEGNO_LOGS")
    (let ([pres (filter (lambda (pre) (and (eq? (car (last-of pre)) 'withExec) (not (member pre logged))))
                        (map (lambda (i) (list-head ch i)) (cdr (iota (+ (length ch) 1)))))])
      (set! logged (append pres logged))
      (let loop ([vs (group-voci pres)])
        (unless (null? vs)
          (run-voce (car vs) (map car (cdr vs)))
          (loop (cdr vs)))))))

(define (voce-of step) (hashtable-ref step-voce step (entry-name)))

(define (group-voci pres)                                ; → ((nome pre …) …), passi consecutivi
  (fold-right (lambda (pre acc)
                (let ([n (voce-of (last-of pre))])
                  (if (and (pair? acc) (eq? (caar acc) n))
                      (cons (cons n (cons pre (cdar acc))) (cdr acc))
                      (cons (list n pre) acc))))
              '() pres))

;; Una voce: i suoi passi in ordine, la prova raccolta a parte. Se un passo fallisce, la riga
;; dice dove, le ultime righe del passo spiegano perché, e si elencano le voci non realizzate.
(define (run-voce v rest)                                ; v: (nome pre …); rest: le voci dopo
  (let ([name (car v)] [t0 (now-ns)] [proof ""])
    (for-each
      (lambda (pre)
        (let* ([step (last-of pre)] [cmd (show-args (step-args step))] [r (run-step pre)])
          (set! proof (string-append proof (format "$ ~a\n" cmd) (car r)))
          (when (pair? (cdr r))
            (let ([pos (hashtable-ref step-pos step #f)])
              (report-voce #f name (if pos (format "~{~a:~a:~a~}" (vector->list pos)) cmd) (cadr r)
                      (- (now-ns) t0) proof (car r) rest)
              (step-failed pos (cadr r) cmd)))))
      (cdr v))
    (report-voce #t name (what (cdr v)) #f (- (now-ns) t0) proof "" '())))

;; Un passo: le righe arrivano dal flusso mentre gira. Un passo in cache non esegue niente e il
;; flusso tace: allora la prova è combinedOutput, stdout e stderr nell'ordine d'arrivo al motore.
;; ponytail: un passo fallito senza flusso ha stdout e stderr separati (le extensions
;; dell'errore): intrecciarli vorrebbe dire rieseguirlo con expect: ANY, fuori dalla cache.
(define (run-step pre)                                   ; → (testo) o (testo exit-code)
  (let ([p (open-output-string)])
    (start-stream!)
    (set! log-port p)
    (let ([before streamed] [e0 eofs])
      (guard (e [(exec-error e)
                 => (lambda (x)
                      (define (ext k) (cond [(assoc k x) => cdr] [else ""]))
                      (settle! before e0 #t)
                      (when (= streamed before) (out (lines (ext "stdout") (ext "stderr"))))
                      (list (lines (get-output-string p)) (ext "exitCode")))])
        (let ([o (submit-leaf (append pre '((combinedOutput))))])
          (settle! before e0)
          (when (= streamed before) (out o))
          (list (lines (get-output-string p))))))))

(define (what pres)                                      ; il lavoro più recente, o «ambiente»
  (let ([work (filter (lambda (pre) (hashtable-ref step-work (last-of pre) #f)) pres)])
    (if (null? work) "ambiente" (show-args (step-args (last-of (last-of work)))))))

(define (show-args args)                                ; il comando, con le virgolette dove servono
  (format "~{~a~^ ~}" (map (lambda (a) (if (memv #\space (string->list a)) (format "~s" a) a)) args)))

(define (lines . ss)                                     ; testi uno dopo l'altro, ciascuno chiuso da un a capo
  (apply string-append (map (lambda (s) (if (or (string=? s "") (char=? (string-ref s (- (string-length s) 1)) #\newline)) s (string-append s "\n"))) ss)))

(define (secs ns) (format "~as" (/ (round (/ ns 100000000)) 10.0)))
(define (pad name) (let ([s (format "~a" name)]) (string-append s (make-string (max 1 (- 12 (string-length s))) #\space))))

(define (last-lines text n)
  (let* ([ls (let loop ([cs (string->list text)] [cur '()] [acc '()])
               (cond [(null? cs) (reverse (if (null? cur) acc (cons (list->string (reverse cur)) acc)))]
                     [(char=? (car cs) #\newline) (loop (cdr cs) '() (cons (list->string (reverse cur)) acc))]
                     [else (loop (cdr cs) (cons (car cs) cur) acc)]))]
         [k (length ls)])
    (if (> k n) (list-tail ls (- k n)) ls)))

;; La riga di una voce. In CI è il titolo di un gruppo chiuso (aperto se la voce fallisce, dove si
;; può) che contiene la prova.
(define sections 0)
(define (report-voce ok name what code dt proof tail rest)
  (let ([line (format "~a ~a~a~@[  exit ~a~]  ~a" (if ok "✓" "✗") (pad name) what code (secs dt))])
    (cond [(env? "GITHUB_ACTIONS") (printf "::group::~a\n~a::endgroup::\n" line proof)]
          [(env? "GITLAB_CI")
           (set! sections (+ sections 1))
           (let ([t (time-second (current-time))])
             (printf "\x1b;[0Ksection_start:~a:voce-~a[collapsed=~a]\r\x1b;[0K~a\n~a\x1b;[0Ksection_end:~a:voce-~a\r\x1b;[0K\n"
                     t sections (if ok "true" "false") line proof t sections))]
          [else (printf "~a\n" line)])
    (unless ok
      (for-each (lambda (l) (printf "      ~a\n" l)) (last-lines tail 10))
      (unless (null? rest) (printf "  non realizzati: ~{~a~^, ~}\n" rest)))
    (flush-output-port)))

;; Un'osservazione (la condizione di un branch): che cosa si è chiesto al mondo, e la risposta.
(define (report-observation ch b)
  (let* ([last (last-of ch)] [exec (and (eq? (car last) 'exitCode) (last-of (list-head ch (- (length ch) 1))))])
    (printf "↳ ~a~a → ~a\n" (pad (voce-of (or exec last)))
            (if exec (format "passa? ~a" (show-args (step-args exec))) (gql-field last))
            (if b "vero" "falso"))
    (flush-output-port)))

(define (summary p dt)                                   ; la riga finale: realizzato, e che cosa
  (let ([last (last-of p)])
    (printf "realizzato in ~a~@[: ~a~]\n" (secs dt)
            (case (car last)
              [(export) (format "esportato ~a" (cadr (assq 'path (cdr last))))]
              [(publish) (format "pubblicato ~a" (cadr (assq 'address (cdr last))))]
              [else #f]))
    (flush-output-port)))

;; --- il flusso: le righe dei comandi appena il motore le riceve (in CI, con DISEGNO_LOGS) ---

(define out-mutex (make-mutex))                          ; il thread del flusso e il principale
(define log-port #f)                                     ; la porta del passo corrente
(define streamed 0)                                      ; righe arrivate dal flusso
(define eofs 0)                                          ; canali chiusi (stdio.eof): due per comando
(define stream-on #f)                                    ; #f: da aprire; un fd: aperto; no: chiuso o assente

(define pending '())                                     ; (istante arrivo . testo), in ordine di istante

(define (now-ns) (let ([t (current-time 'time-utc)]) (+ (* (time-second t) 1000000000) (time-nanosecond t))))

(define (start-stream!)
  (unless stream-on
    (set! log-port #f)                                   ; finché è #f, on-log scarta
    (set! stream-on (guard (e [#t 'no])
                      (log-stream (string->number (getenv "DAGGER_SESSION_PORT")) (getenv "DAGGER_SESSION_TOKEN") on-log)))
    (when (number? stream-on)
      (let ([fd stream-on])                             ; finché il flusso è questo
        (fork-thread (lambda ()
                       (let loop ()
                         (sleep (make-time 'time-duration 50000000 0))
                         (when (eqv? stream-on fd) (flush! (- (now-ns) window)) (loop))))))
      ;; All'iscrizione il motore rimanda i log già prodotti nella sessione, tutti e subito: si
      ;; lasciano passare prima di ascoltare. Filtrarli per istante vorrebbe dire confrontare
      ;; l'orologio del motore con quello locale.
      ;; ponytail: 200 ms, una volta per run; in un run vero lo storico è vuoto, il flusso si
      ;; apre al primo passo, prima di ogni comando.
      (sleep (make-time 'time-duration 200000000 0)))))

;; Il motore manda stdout e stderr a pacchetti separati: una riga di stderr può arrivare 200 ms
;; dopo una di stdout scritta più tardi. Ogni record porta l'istante (del motore) in cui la riga
;; è stata letta dalla pipe: il buffer è in ordine di quell'istante, e ogni riga esce quando è
;; arrivata da almeno una finestra (sull'orologio locale). I due orologi non si confrontano mai.
;; ponytail: finestra fissa di 300 ms; un pacchetto più in ritardo esce fuori posto.
(define window 300000000)

(define (flush! until)                                   ; stampa le righe in testa arrivate entro until
  (with-mutex out-mutex
    (let loop ()
      (when (and (pair? pending) (<= (cadar pending) until))
        (emit (cddar pending))
        (set! pending (cdr pending))
        (loop)))))

(define (insert-pending t s)                             ; in ordine; a parità, nell'ordine d'arrivo
  (let loop ([ps pending])
    (cond [(or (null? ps) (< t (caar ps))) (cons (cons* t (now-ns) s) ps)]
          [else (cons (car ps) (loop (cdr ps)))])))

;; Il flusso si chiude prima della sessione: Dagger non sopporta una richiesta ancora aperta.
(define (stop-stream!)
  (when (number? stream-on) (log-stream-stop stream-on) (set! stream-on #f)))   ; un altro run lo riapre

;; Solo l'output dei comandi (stdio.stream); non i valori restituiti, che il motore ripete come
;; log verbosi (dagger.io/logs.verbose): combinedOutput uscirebbe due volte.
(define (on-log rec)
  (let ([body (json-field (json-field rec "body" '()) "stringValue" #f)]
        [keys (map (lambda (a) (json-field a "key" #f)) (json-field rec "attributes" '()))]
        [t (or (string->number (json-field rec "timeUnixNano" "0")) 0)])
    (when (and body log-port (member "stdio.stream" keys) (not (member "dagger.io/logs.verbose" keys)))
      (with-mutex out-mutex
        (if (member "stdio.eof" keys)
            (set! eofs (+ eofs 1))
            (begin (set! streamed (+ streamed 1)) (set! pending (insert-pending t body))))))))

(define (out s) (with-mutex out-mutex (emit s)))
(define (emit s)
  (unless (string=? s "")
    (display s log-port) (flush-output-port log-port)))

;; Le ultime righe possono arrivare dopo la risposta: si aspetta che il comando chiuda i canali.
(define (settle! s0 e0 . ran)                            ; s0, e0: righe e eof a inizio passo; ran: il passo è fallito, quindi ha girato
  (when (number? stream-on)
    (let loop ([k 0])
      (sleep (make-time 'time-duration 50000000 0))
      (unless (or (>= (- eofs e0) 2)                     ; stdout e stderr chiusi: il comando ha finito
                  (and (>= k 6) (null? ran) (= streamed s0) (= eofs e0))   ; 300 ms, la finestra del flusso, senza niente: in cache (un fallimento non lo è)
                  (> k 40))                             ; ponytail: 2 s, poi si chiude comunque
        (loop (+ k 1))))
    (flush! +inf.0)))                                     ; il passo è finito: tutto il buffer

;; Un passo fallito: dove sta nel sorgente, con che exit code, quale comando. Su GitHub anche
;; un'annotazione, che compare sul file e sulla riga.
(define (step-failed pos code title)
  (let ([what (format "passo fallito (exit ~a): ~a" code title)] [at (and pos (vector->list pos))])
    (when (env? "GITHUB_ACTIONS")
      (printf "::error~@[ ~{file=~a,line=~a,col=~a~}~]::~a\n" at what))
    (error 'disegno (format "~@[~{~a:~a:~a~}: ~]~a" at what))))

(define (resolve-live ch) (log-steps ch) (submit-leaf (append ch '((id)))))
(define (resolve-dry ch) (format "<~a>" (plan->graphql ch)))

;; ponytail: un'osservazione booleana è un Boolean GraphQL o un exit code (vero se 0).
(define (observe-live ch)
  (log-steps ch)
  (let* ([r (submit-leaf ch)]
         [b (cond [(boolean? r) r] [(number? r) (= r 0)] [else (oops "osservazione non booleana: ~s" r)])])
    (when (env? "DISEGNO_LOGS") (report-observation ch b))
    b))

(define (run entry)
  (parameterize ([observe observe-live] [entry-name entry])
    (guard (e [(exec-error e) => (lambda (x)                ; anche senza log: quale passo, e dove
                                   (let ([cmd (cdr (assoc "cmd" x))])
                                     (step-failed (cmd-pos cmd) (cdr (assoc "exitCode" x)) (show-args cmd))))])
      (dynamic-wind void
        (lambda ()
          (let* ([t0 (now-ns)] [p (plan resolve-live entry)])
            (log-steps p)
            (let ([r (submit-leaf p)])
              (when (env? "DISEGNO_LOGS") (summary p (- (now-ns) t0)))
              r)))
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
