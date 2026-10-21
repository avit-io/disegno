;; Plan: main is evaluated (purely) into data, a tree of Obj constructors, which becomes GraphQL
;; here. The constructor Type.kebab-field is the field typeField; the names of its explicit
;; binders are the arguments; for methods the first argument (self) is the object.
;; Object arguments are passed by ID: `resolve` gets their chain and returns the ID (live) or a
;; placeholder (dry).
;; branch is the only point where the engine decides: `observe` gets the condition's chain and
;; returns the outcome. Both branches are in the plan; at run time only one is taken.

(define observe (make-parameter (lambda (ch) (oops "branch needs a Dagger session"))))

;; A relative Host or Export resolves against the program's directory, not the current one.
(define program-dir (make-parameter ""))

(define (explicit sp) (map car (filter (lambda (a) (eq? (cdr a) 'e)) sp)))

(define (map-ltr f xs ys)                                ; map with a guaranteed order, left to right
  (reverse (fold-left (lambda (acc x y) (cons (f x y) acc)) '() xs ys)))

(define (split-dots s)
  (let loop ([cs (string->list s)] [cur '()] [acc '()])
    (cond [(null? cs) (reverse (cons (list->string (reverse cur)) acc))]
          [(char=? (car cs) #\.) (loop (cdr cs) '() (cons (list->string (reverse cur)) acc))]
          [else (loop (cdr cs) (cons (car cs) cur) acc)])))

(define (camel s)                                        ; with-new-file → withNewFile (as in gen.ss)
  (let loop ([cs (string->list s)] [up #f])
    (cond [(null? cs) ""]
          [(char=? (car cs) #\-) (loop (cdr cs) #t)]
          [else (string-append (string (if up (char-upcase (car cs)) (car cs))) (loop (cdr cs) #f))])))

(define (node v)                                         ; → the constructor's name if v is a plan node
  (and (eq? (car v) 'vglob)
       (let ([g (gget (cadr v))]) (and g (eq? (g-kind g) 'con) (bi? (g-info g) 'obj) (cadr v)))))

(define (arg-names c)                                    ; the constructor's explicit binders
  (let loop ([t (force (g-type (gget c)))] [l 0])
    (if (eq? (car t) 'vpi)
        (let ([rest (loop (force (pi-cod t (vvar l))) (+ l 1))])
          (if (eq? (caddr t) 'e) (cons (cadr t) rest) rest))
        '())))

(define (pick v resolve)                                 ; resolves the branches at the head of v
  (let ([v (force v)])
    (if (eq? (node v) 'branch)
        (let ([xs (explicit (caddr v))])
          (pick (if ((observe) (chain (car xs) resolve)) (cadr xs) (caddr xs)) resolve))
        v)))

;; For each step of the chain we remember: where it is in the source and which item it belongs to
;; (a with-exec marked by the checker), and whether it is work, that is it depends on an input of
;; the program (a Host), or preparation of the environment.
(define step-pos (make-eq-hashtable))
(define step-item (make-eq-hashtable))
(define step-work (make-eq-hashtable))
(define step-question (make-eq-hashtable))               ; an observation: the question with a docstring that asks it
(define (located v ch)
  (let ([last (list-ref ch (- (length ch) 1))])
    (cond [(v-pos v) => (lambda (p) (hashtable-set! step-pos last p))])
    (hashtable-set! step-work last (on-input? v))
    (cond [(v-name v) => (lambda (n) (hashtable-set! step-item last n))])
    (cond [(v-question v) => (lambda (q) (hashtable-set! step-question last q))]))
  ch)

(define input-memo (make-eq-hashtable))
(define (on-input? v)                                    ; does the value depend on a Host?
  (let ([v (force v)])
    (and (eq? (car v) 'vglob)
         (or (eq? (cadr v) '%host-dir)
             (let ([m (hashtable-ref input-memo v '?)])
               (if (eq? m '?)
                   (let ([r (exists (lambda (a) (on-input? (car a))) (caddr v))]) (hashtable-set! input-memo v r) r)
                   m))))))

(define (chain v resolve)
  (let* ([v (pick v resolve)] [c (node v)])
    (unless c (oops "plan not static: ~s" (sexp '() (reify 0 v))))
    (let ([args (explicit (caddr v))] [names (arg-names c)])
      (define (field f names args . fixed)
        (cons f (append (map-ltr (lambda (n a) (list n (gql-arg a resolve))) names args) fixed)))
      (define (method f . fixed)                        ; let*: requests go out left to right
        (let* ([recv (chain (car args) resolve)])
          (append recv (list (apply field f (cdr names) (cdr args) fixed)))))
      (located v
        (case c
          [(%host-dir) (list '(host) (field 'directory names args))]
          [(%host-secret) (list `(secret (uri ,(string-append "env://" (gql-arg (car args) resolve)))))]   ; the name, never the value
          [(try-exec) (method 'withExec '(expect ANY))]
          [(cache-volume) (list (field 'cacheVolume names args))]
          [(passes?) (method 'exitCode)]
          [(probe) (append (fresh-exec v resolve '(expect ANY)) '((exitCode)))]   ; the world, outside the cache
          [(secret-from) ((fetch-secret) v resolve)]                          ; dry the command, live setSecret
          [(with-fresh-exec) (fresh-exec v resolve)]                        ; with-exec outside the cache
          ;; A secret's value is not in BuildKit's cache key: with secrets the build also gets
          ;; DISEGNO_RUN, so an ARG DISEGNO_RUN before the RUN that reads the secret reruns it.
          [(Directory.docker-build)
           (let* ([ch (method 'dockerBuild)] [f (list-ref ch (- (length ch) 1))])
             (if (null? (cadr (assq 'secrets (cdr f))))
                 ch
                 (let ([run `(%input (name . "DISEGNO_RUN") (value . ,(run-id)))])
                   (append (list-head ch (- (length ch) 1))
                           (list (cons (car f) (map (lambda (a) (if (eq? (car a) 'buildArgs) (list 'buildArgs (append (cadr a) (list run))) a)) (cdr f))))))))]
          [(overlay replace publish apply then skip start otherwise fail) (oops "an output (Export) goes at the top of the plan, or in then and branch")]
          [else (let ([segs (split-dots (symbol->string c))])
                  (if (string=? (car segs) "Query")
                      (list (field (string->symbol (camel (cadr segs))) names args))
                      (method (string->symbol (camel (cadr segs))))))])))))

(define (gql-arg v resolve)                              ; string, natural, boolean, list or object (by ID)
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
          ;; an input object of the schema: (build-arg n v) is {name: n, value: v}
          [(and (eq? (car v) 'vglob) (eq? (cadr v) 'build-arg))
           (let ([xs (explicit (caddr v))]) `(%input (name . ,(gql-arg (car xs) resolve)) (value . ,(gql-arg (cadr xs) resolve))))]
          ;; a refined value (Image, Segment, Arg…) goes to the engine as its first field
          [(and (eq? (car v) 'vglob) (eq? (g-kind (gget (cadr v))) 'con) (pair? (explicit (caddr v))))
           (gql-arg (car (explicit (caddr v))) resolve)]
          [else (oops "argument not static: ~s" (sexp '() (reify 0 v)))])))

(define (abs-string v resolve)                           ; (/ (/ root "go") "pkg") → "/go/pkg"
  (let loop ([v (force v)] [acc '()])
    (cond [(bi? (cadr v) 'root) (if (null? acc) "/" (apply string-append (map (lambda (s) (string-append "/" s)) acc)))]
          [(bi? (cadr v) 'slash) (let ([xs (explicit (caddr v))]) (loop (force (car xs)) (cons (gql-arg (cadr xs) resolve) acc)))]
          [else (oops "path not static: ~s" (sexp '() (reify 0 v)))])))

;; main : (→ [x (Host "p")] ... (Export Dir)). The plan's outputs are realized in order:
;; branch is resolved when reached, then realizes a and then b, skip does nothing; each leaf
;; output (export, publish, effect) is a chain that emit gets. Live, emit runs it at once, so an
;; observation after an effect sees the world after the effect.
;; main's inputs, from its signature: (Host "path") a directory, (Host-secret "NAME") a secret,
;; (Host-env "NAME" "default") a parameter, read from the environment when the plan is built.
(define (main-input dom)                                 ; → the argument's value, or an error
  (define (str? t) (and (pair? t) (eq? (car t) 'str)))
  (define (head-is? t k) (equal? t `(glob ,(bi k))))
  (cond
    [(and (eq? (car dom) 'app) (str? (caddr dom)) (head-is? (cadr dom) 'host))
     (list 'vglob '%host-dir (list (cons (list 'vstr (in-dir (program-dir) (cadr (caddr dom)))) 'e)))]
    [(and (eq? (car dom) 'app) (str? (caddr dom)) (head-is? (cadr dom) 'host-secret))
     (let ([s (cadr (caddr dom))])
       (unless (env-name? s) (oops "Host-secret: «~a» is not the name of an environment variable" s))
       (list 'vglob '%host-secret (list (cons (list 'vstr s) 'e))))]
    [(and (eq? (car dom) 'app) (str? (caddr dom)) (pair? (cadr dom)) (eq? (car (cadr dom)) 'app)
          (str? (caddr (cadr dom))) (head-is? (cadr (cadr dom)) 'host-env))
     (let ([s (cadr (caddr (cadr dom)))] [default (cadr (caddr dom))])
       (unless (env-name? s) (oops "Host-env: «~a» is not the name of an environment variable" s))
       (list 'vstr (let ([v (getenv s)]) (if (and v (not (string=? v ""))) v default))))]
    [(let ([sp (spine dom)]) (and (= (length sp) 4) (head-is? (car sp) 'host-choice) (str? (cadr sp)) sp))
     => (lambda (sp) (choice (cadr (cadr sp)) (caddr sp) (cadddr sp)))]
    [else (oops "main's arguments must be (Host \"path\"), (Host-secret \"NAME\"), (Host-env \"NAME\" \"default\") or (Host-choice \"NAME\" Type default)")]))

(define (spine t)                                        ; (f a b c) → (f a b c), from the app nodes
  (let loop ([t t] [as '()])
    (if (and (pair? t) (eq? (car t) 'app)) (loop (cadr t) (cons (caddr t) as)) (cons t as))))

;; (Host-choice "NAME" Type default): the value is the constructor of Type named like the
;; variable; a name that is not there stops building the plan, before anything runs.
(define (choice s ty default)
  (unless (env-name? s) (oops "Host-choice: «~a» is not the name of an environment variable" s))
  (let* ([d (and (eq? (car ty) 'glob) (gget (cadr ty)))]
         [ks (and d (eq? (g-kind d) 'data) (g-info d))])
    (unless (and ks (for-all (lambda (k) (eq? (car (force (g-type (gget k)))) 'vglob)) ks))
      (oops "Host-choice ~a: the type must be a data of constructors without arguments only" s))
    (let ([v (getenv s)])
      (if (or (not v) (string=? v ""))
          (ev '() default)
          (let ([k (find (lambda (k) (string=? (symbol->string k) v)) ks)])
            (unless k (oops "~a: «~a» is not one of ~a" s v (join-names ks)))
            (ev '() `(glob ,k)))))))

(define (join-names ks)
  (fold-left (lambda (acc k) (string-append acc ", " (symbol->string k))) (symbol->string (car ks)) (cdr ks)))

(define (entry-value main)
  (let* ([sig (or (hashtable-ref sigs main #f) (oops "~a is missing" main))]
         [inputs (let loop ([t sig])
                   (if (eq? (car t) 'pi)
                       (begin (unless (eq? (caddr t) 'e) (oops "main's arguments are explicit"))
                              (cons (main-input (cadddr t)) (loop (list-ref t 4))))
                       '()))])
    (vapp-sp (ev '() `(glob ,main)) (map (lambda (h) (cons h 'e)) inputs))))

;; An effect and an observation of the world are not cached: a new environment variable on each
;; run, right before the command, so the preparation of the environment stays cached.
(define run-id (make-parameter "<run>"))

;; Unique per occurrence: two identical fresh commands in the same run (two clones of the same
;; branch, a probe repeated after an effect) stay two commands, not one cached.
(define fresh-count 0)
(define (fresh-nonce) (set! fresh-count (+ fresh-count 1)) (format "~a-~a" (run-id) fresh-count))

;; Secrets read at run time: (secret-from c cmd). Dry, the plan shows the command, never the
;; value. Live, when a step uses the secret, cmd runs in c outside the cache, with its output in
;; a file (not in the logs); the runner reads the file and hands it to Dagger with setSecret, which
;; masks it from then on. The value passes through the runner only, never the language; a secret
;; is read once per run.
;; ponytail: the file stays in the (local) engine's cache; a shared engine would need cleaning.
(define secret-memo (make-hashtable string-hash string=?))

(define (fetch-dry v resolve)
  (let ([xs (explicit (caddr v))])
    (list `(secretFrom (name ,(gql-arg (caddr xs) resolve)) (args ,(gql-arg (cadr xs) resolve))))))

(define (fetch-live v resolve)
  (let* ([xs (explicit (caddr v))] [recv (chain (car xs) resolve)] [cmd (gql-arg (cadr xs) resolve)]
         ;; the key from the dry plan: live IDs change on every resolution, and the secret would be read again
         [key (string-append (gql-arg (caddr xs) resolve) " "
                (parameterize ([fetch-secret fetch-dry])
                  (plan->graphql (append (chain (car xs) resolve-dry) (list `(withExec (args ,cmd)))))))])
    (or (hashtable-ref secret-memo key #f)
        (let* ([text (submit-leaf (append recv (list `(withEnvVariable (name "DISEGNO_RUN") (value ,(fresh-nonce)))
                                                     `(withExec (args ("sh" "-c" "\"$@\" > /tmp/disegno-secret" "sh" ,@cmd)))
                                                     '(file (path "/tmp/disegno-secret")) '(contents))))]
               [n (string-length text)]
               [text (if (and (> n 0) (char=? (string-ref text (- n 1)) #\newline)) (substring text 0 (- n 1)) text)]
               [ch (list `(setSecret (name ,(gql-arg (caddr xs) resolve)) (plaintext ,text)))])
          (when (env? "DISEGNO_LOGS")
            (secret-line (format "secret ~a read" (gql-arg (caddr xs) resolve))))   ; the command is in disegno plan
          (hashtable-set! secret-memo key ch)
          ch))))

(define fetch-secret (make-parameter fetch-dry))

(define (env-name? s)                                    ; AWS_ACCESS_KEY_ID: letters, digits, _, not a digit first
  (let ([cs (string->list s)])
    (and (pair? cs) (not (char-numeric? (car cs)))
         (for-all (lambda (c) (or (char-alphabetic? c) (char-numeric? c) (char=? c #\_))) cs))))
(define (fresh-exec v resolve . fixed)                   ; (apply c cmd) or (probe c cmd) → chain up to the withExec
  (let* ([xs (explicit (caddr v))] [recv (chain (car xs) resolve)]
         [ch (located v (append recv (list `(withEnvVariable (name "DISEGNO_RUN") (value ,(fresh-nonce)))
                                           `(withExec (args ,(gql-arg (cadr xs) resolve)) ,@fixed))))])
    (hashtable-set! step-work (last-of ch) #t)           ; an effect is work: the report shows the command
    ch))

(define realize-dry (make-parameter #t))              ; #f live: otherwise really tries

(define (realize v resolve emit)
  (let ([v (pick v resolve)])
    (case (node v)
      [(then) (let ([xs (explicit (caddr v))]) (realize (car xs) resolve emit) (realize (cadr xs) resolve emit))]
      [(otherwise)                                       ; if a fails, b; then a's error
       (let ([xs (explicit (caddr v))])
         (if (realize-dry)
             (begin (realize (car xs) resolve emit) (emit 'otherwise) (realize (cadr xs) resolve emit))
             (guard (e [#t (realize (cadr xs) resolve emit) (raise e)])
               (realize (car xs) resolve emit))))]
      [(skip) (void)]
      [(fail)                                            ; dry a line of the plan, live the error, with the position
       (let ([msg (gql-arg (car (explicit (caddr v))) resolve)])
         (if (realize-dry) (emit msg) (parameterize ([here (v-pos v)]) (oops "~a" msg))))]
      [(overlay replace)                                 ; export to the host; replace is with wipe
       (let* ([path (in-dir (program-dir) (gql-arg (car (explicit (caddr v))) resolve))]
              [dir (chain (cadr (explicit (caddr v))) resolve)])
         (emit (append dir (list `(export (path ,path) (wipe ,(eq? (node v) 'replace)))))))]
      [(publish)                                         ; publishing the image to a registry
       (let* ([ctr (chain (car (explicit (caddr v))) resolve)])
         (emit (append ctr (list `(publish (address ,(gql-arg (cadr (explicit (caddr v))) resolve)))))))]
      [(apply) (emit (append (fresh-exec v resolve) '((exitCode))))]
      [(start) (emit (append (chain (car (explicit (caddr v))) resolve) '((start))))]   ; the service stays alive for the session
      [else (oops "the plan must return an Export")])))

(define (exits resolve . entry)                          ; → the outputs' chains, in order
  (let ([acc '()])
    (realize (entry-value (if (null? entry) 'main (car entry))) resolve (lambda (ch) (when (pair? ch) (set! acc (cons ch acc)))))
    (reverse acc)))

(define (plan resolve . entry)                           ; a plan with a single output: its chain
  (let ([es (apply exits resolve entry)])
    (if (= (length es) 1) (car es) (oops "the plan has ~a outputs: use exits" (length es)))))

;; --- execution ---

;; --- the report: with DISEGNO_LOGS, one line per item of the program ---
;; The log says what was not known before running: how each item went, how long it took, what
;; was observed. The plan and its properties were known already. An item is a definition of the
;; program that builds a piece of the plan (chez, test, publish); steps that no definition named
;; belong to the entry point. The commands' output is the proof: in CI it sits in the item's
;; collapsed group, elsewhere it shows only if the item fails.
;; Dagger is lazy and cached: asking for the output of the prefix ending in a withExec runs the
;; chain up to there, and the final request redoes nothing.

(define (env? name)                                      ; defined and not empty: "" counts as absent
  (let ([v (getenv name)]) (and v (not (string=? v "")))))

(define entry-name (make-parameter 'main))
(define logged '())                                      ; prefixes already run

(define (last-of l) (list-ref l (- (length l) 1)))
(define (step-args step) (cadr (assq 'args (cdr step))))

(define (log-steps ch)
  (when (env? "DISEGNO_LOGS")
    (let ([pres (filter (lambda (pre) (and (eq? (car (last-of pre)) 'withExec) (not (member pre logged))))
                        (map (lambda (i) (list-head ch i)) (cdr (iota (+ (length ch) 1)))))])
      (set! logged (append pres logged))
      (let loop ([vs (group-items pres)])
        (unless (null? vs)
          (run-item (car vs) (map car (cdr vs)))
          (loop (cdr vs)))))))

(define (item-of step) (hashtable-ref step-item step (entry-name)))

(define (group-items pres)                                ; → ((name pre …) …), consecutive steps
  (fold-right (lambda (pre acc)
                (let ([n (item-of (last-of pre))])
                  (if (and (pair? acc) (eq? (caar acc) n))
                      (cons (cons n (cons pre (cdar acc))) (cdr acc))
                      (cons (list n pre) acc))))
              '() pres))

;; An item: its steps in order, the proof collected apart. If a step fails, the line says
;; where, the step's last lines explain why, and the items not realized are listed.
(define (run-item v rest)                                ; v: (name pre …); rest: the items after
  (let ([name (car v)] [t0 (now-ns)] [proof ""])
    (for-each
      (lambda (pre)
        (let* ([step (last-of pre)] [cmd (show-args (step-args step))] [r (run-step pre)])
          (set! proof (string-append proof (format "$ ~a\n" cmd) (car r)))
          (when (pair? (cdr r))
            (let ([pos (hashtable-ref step-pos step #f)])
              (report-item #f name (if pos (format "~{~a:~a:~a~}" (vector->list pos)) cmd) (cadr r)
                      (- (now-ns) t0) proof (car r) rest)
              (step-failed pos (cadr r) cmd)))))
      (cdr v))
    (report-item #t name (what (cdr v)) #f (- (now-ns) t0) proof "" '())))

;; An effect or an observation of the world (fresh-exec): the command right after DISEGNO_RUN, never cached.
(define (fresh? pre)
  (let ([n (length pre)])
    (and (>= n 2)
         (let ([s (list-ref pre (- n 2))]) (and (eq? (car s) 'withEnvVariable) (equal? (assq 'name (cdr s)) '(name "DISEGNO_RUN")))))))

;; A step: its lines arrive from the stream while it runs. A cached step runs nothing and the
;; stream is silent: then the proof is combinedOutput, stdout and stderr in the engine's arrival order.
;; ponytail: a failed step without a stream has stdout and stderr apart (the error's
;; extensions): interleaving them would mean rerunning it with expect: ANY, outside the cache.
(define (run-step pre)                                   ; → (text) or (text exit-code)
  (let ([p (open-output-string)])
    (start-stream!)
    (set! log-port p)
    (let ([before streamed] [e0 eofs])
      (guard (e [(exec-error e)
                 => (lambda (x)
                      (define (ext k) (cond [(assoc k x) => cdr] [else ""]))
                      (settle! before e0 #t)
                      (when (= streamed before) (out (lines (ext "stdout") (ext "stderr"))))
                      (list (lines (ext "stdout") (ext "stderr")) (ext "exitCode")))])   ; the last lines from the error: complete, without late lines of other steps
        (let ([o (submit-leaf (append pre '((combinedOutput))))])
          (apply settle! before e0 (if (fresh? pre) '(#t) '()))   ; an effect ran: wait for its lines
          (when (= streamed before) (out o))
          (list (lines (get-output-string p))))))))

(define (what pres)                                      ; the most recent work, or «environment»
  (let ([work (filter (lambda (pre) (hashtable-ref step-work (last-of pre) #f)) pres)])
    (if (null? work) "environment" (show-args (step-args (last-of (last-of work)))))))

(define (show-args args)                                ; the command, quoted where needed
  ;; a long library script (sh -c "…" arguments) reads from its arguments: the full text is in
  ;; disegno plan, and a failed step says where it is in the source
  (let ([args (if (and (>= (length args) 3) (equal? (car args) "sh") (equal? (cadr args) "-c") (> (string-length (caddr args)) 120))
                  (cons* "sh" "-c" "…" (cdddr args))
                  args)])
    (format "~{~a~^ ~}" (map (lambda (a) (if (memv #\space (string->list a)) (format "~s" a) a)) args))))

(define (lines . ss)                                     ; texts one after the other, each ended by a newline
  (apply string-append (map (lambda (s) (if (or (string=? s "") (char=? (string-ref s (- (string-length s) 1)) #\newline)) s (string-append s "\n"))) ss)))

(define (secs ns) (format "~as" (/ (round (/ ns 100000000)) 10.0)))
(define (pad name)                                       ; an item's name, or its docstring
  (let ([s (format "~a" (or (and (symbol? name) (item-doc name)) name))]) (string-append s (make-string (max 2 (- 12 (string-length s))) #\space))))

(define (last-lines text n)
  (let* ([ls (let loop ([cs (string->list text)] [cur '()] [acc '()])
               (cond [(null? cs) (reverse (if (null? cur) acc (cons (list->string (reverse cur)) acc)))]
                     [(char=? (car cs) #\newline) (loop (cdr cs) '() (cons (list->string (reverse cur)) acc))]
                     [else (loop (cdr cs) (cons (car cs) cur) acc)]))]
         [k (length ls)])
    (if (> k n) (list-tail ls (- k n)) ls)))

;; An item with a docstring is a single line: its consecutive steps (even from different chains)
;; extend it, and the observations and secrets about it go below it. The line comes out when
;; another item, a failure or the end arrives.
(define held #f)                                         ; (name time proof sub-lines), pending
(define waiting '())                                     ; secrets read before an item opens
(define (report-item ok name what code dt proof tail rest)
  (if (and ok (item-doc name))
      (if (and held (eq? (car held) name))
          (set! held (list name (+ (cadr held) dt) (string-append (caddr held) proof) (cadddr held)))
          (begin (release!) (set! held (list name dt proof waiting)) (set! waiting '())))
      (begin (release!) (print-waiting) (print-item ok name what code dt proof tail rest))))
(define (release!)
  (when held
    (let ([h held])
      (set! held #f)
      (print-item #t (car h) "" #f (cadr h) (caddr h) "" '())
      (for-each (lambda (s) (printf "    ↳ ~a\n" s)) (reverse (cadddr h)))
      (flush-output-port))))
(define (print-waiting)
  (for-each (lambda (s) (printf "↳ ~a\n" s)) (reverse waiting))
  (set! waiting '())
  (flush-output-port))
(define (attach! text) (set! held (list (car held) (cadr held) (caddr held) (cons text (cadddr held)))))
(define (sub-line name text)                             ; an observation: below its item
  (if (and held (eq? (car held) name))
      (attach! text)
      (begin (release!) (print-waiting) (printf "↳ ~a~a\n" (if (and (symbol? name) (item-doc name)) (pad name) "") text) (flush-output-port))))
;; ponytail: a secret goes below the open item, or waits for the next: where it was born does not
;; say which step needs it. One read for the next item, while the previous is open, ends up below that.
(define (secret-line text) (if held (attach! text) (set! waiting (cons text waiting))))

;; An item's line. In CI it is the title of a collapsed group (open if the item fails, where
;; possible) holding the proof.
(define sections 0)
(define (print-item ok name what code dt proof tail rest)
  (let ([line (format "~a ~a~a~@[  exit ~a~]  ~a" (if ok "✓" "✗") (pad name) (if (and ok (item-doc name)) "" what) code (secs dt))])   ; with a docstring, the command is in the proof
    (cond [(env? "GITHUB_ACTIONS") (printf "::group::~a\n~a::endgroup::\n" line proof)]
          [(env? "GITLAB_CI")
           (set! sections (+ sections 1))
           (let ([t (time-second (current-time))])
             (printf "\x1b;[0Ksection_start:~a:item-~a[collapsed=~a]\r\x1b;[0K~a\n~a\x1b;[0Ksection_end:~a:item-~a\r\x1b;[0K\n"
                     t sections (if ok "true" "false") line proof t sections))]
          [else (printf "~a\n" line)])
    (unless ok
      (for-each (lambda (l) (printf "      ~a\n" l)) (last-lines tail 10))
      (unless (null? rest) (printf "  not realized: ~{~a~^, ~}\n" rest)))
    (flush-output-port)))

;; An observation (a branch's condition): what was asked of the world, and the answer.
(define (report-observation ch b)
  (let* ([last (last-of ch)] [exec (and (eq? (car last) 'exitCode) (last-of (list-head ch (- (length ch) 1))))])
    (let ([n (item-of (or exec last))] [q (hashtable-ref step-question (or exec last) #f)])
      (if q
          (let ([text (format "~a ~a" (item-doc q) (if b "yes" "no"))]) (if (and held (eq? (car held) n)) (attach! text) (sub-line #f text)))
          (sub-line n (format "~a → ~a" (if exec (format "passes? ~a" (show-args (step-args exec))) (gql-field last)) (if b "true" "false")))))))

(define (outcome ch)                                     ; what an output did, in words
  (let ([last (last-of ch)])
    (case (car last)
      [(export) (format "exported ~a" (cadr (assq 'path (cdr last))))]
      [(publish) (format "published ~a" (cadr (assq 'address (cdr last))))]
      [(start) "service started"]
      [(exitCode) (let ([step (last-of (list-head ch (- (length ch) 1)))])   ; the item's docstring, if any
                    (or (item-doc (item-of step)) (format "effect ~a" (show-args (step-args step)))))]
      [else "?"])))

(define (outcomes done)                                  ; the outputs in words, without repeating the same item
  (format "~{~a~^, ~}" (fold-right (lambda (o acc) (if (and (pair? acc) (string=? o (car acc))) acc (cons o acc))) '() (map outcome done))))

(define (summary done dt)                                ; the last line: realized, and what
  (release!) (print-waiting)
  (printf "realized in ~a~@[: ~a~]\n" (secs dt) (and (pair? done) (outcomes done)))
  (flush-output-port))

;; --- the stream: the commands' lines as soon as the engine gets them (in CI, with DISEGNO_LOGS) ---

(define out-mutex (make-mutex))                          ; the stream's thread and the main one
(define log-port #f)                                     ; the current step's port
(define streamed 0)                                      ; lines that came from the stream
(define eofs 0)                                          ; closed channels (stdio.eof): two per command
(define stream-on #f)                                    ; #f: to open; an fd: open; no: closed or absent

(define pending '())                                     ; (instant arrival . text), in order of instant

(define (now-ns) (let ([t (current-time 'time-utc)]) (+ (* (time-second t) 1000000000) (time-nanosecond t))))

(define (start-stream!)
  (unless stream-on
    (set! log-port #f)                                   ; while #f, on-log discards
    (set! stream-on (guard (e [#t 'no])
                      (log-stream (string->number (getenv "DAGGER_SESSION_PORT")) (getenv "DAGGER_SESSION_TOKEN") on-log)))
    (when (number? stream-on)
      (let ([fd stream-on])                             ; as long as the stream is this one
        (fork-thread (lambda ()
                       (let loop ()
                         (sleep (make-time 'time-duration 50000000 0))
                         (when (eqv? stream-on fd) (flush! (- (now-ns) window)) (loop))))))
      ;; On subscribing the engine resends the logs already produced in the session, all at once:
      ;; let them pass before listening. Filtering them by instant would mean comparing the
      ;; engine's clock with the local one.
      ;; ponytail: 200 ms, once per run; in a real run the history is empty, the stream opens at
      ;; the first step, before any command.
      (sleep (make-time 'time-duration 200000000 0)))))

;; The engine sends stdout and stderr in separate packets: a stderr line can arrive 200 ms after a
;; stdout line written later. Each record carries the (engine's) instant the line was read from
;; the pipe: the buffer is in order of that instant, and each line comes out once it has been
;; there for at least a window (on the local clock). The two clocks are never compared.
;; ponytail: a fixed 300 ms window; a later packet comes out of place.
(define window 300000000)

(define (flush! until)                                   ; prints the head lines that arrived by until
  (with-mutex out-mutex
    (let loop ()
      (when (and (pair? pending) (<= (cadar pending) until))
        (emit (cddar pending))
        (set! pending (cdr pending))
        (loop)))))

(define (insert-pending t s)                             ; in order; on ties, in arrival order
  (let loop ([ps pending])
    (cond [(or (null? ps) (< t (caar ps))) (cons (cons* t (now-ns) s) ps)]
          [else (cons (car ps) (loop (cdr ps)))])))

;; The stream closes before the session: Dagger does not bear a request still open.
(define (stop-stream!)
  (when (number? stream-on) (log-stream-stop stream-on) (set! stream-on #f)))   ; another run reopens it

;; Only the commands' output (stdio.stream); not the returned values, which the engine repeats as
;; verbose logs (dagger.io/logs.verbose): combinedOutput would come out twice.
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

;; The last lines can arrive after the response: wait for the command to close its channels.
(define (settle! s0 e0 . ran)                            ; s0, e0: lines and eofs at the step's start; ran: the step failed, so it ran
  (when (number? stream-on)
    (let loop ([k 0])
      (sleep (make-time 'time-duration 50000000 0))
      (unless (or (>= (- eofs e0) 2)                     ; stdout and stderr closed: the command is done
                  (and (>= k 6) (null? ran) (= streamed s0) (= eofs e0))   ; 300 ms, the stream's window, with nothing: cached (a failure is not)
                  (> k 40))                             ; ponytail: 2 s, then it closes anyway
        (loop (+ k 1))))
    (flush! +inf.0)))                                     ; the step is done: the whole buffer

;; A failed step: where it is in the source, with which exit code, which command. On GitHub also
;; an annotation, shown on the file and line.
(define (step-failed pos code title)
  (let ([what (format "step failed (exit ~a): ~a" code title)] [at (and pos (vector->list pos))])
    (when (env? "GITHUB_ACTIONS")
      (printf "::error~@[ ~{file=~a,line=~a,col=~a~}~]::~a\n" at what))
    (error 'disegno (format "~@[~{~a:~a:~a~}: ~]~a" at what))))

(define (resolve-live ch) (log-steps ch) (submit-leaf (append ch '((id)))))
(define (resolve-dry ch) (format "<~a>" (plan->graphql ch)))

;; ponytail: a boolean observation is a GraphQL Boolean or an exit code (true if 0).
(define (observe-live ch)
  (log-steps ch)
  (let* ([r (submit-leaf ch)]
         [b (cond [(boolean? r) r] [(number? r) (= r 0)] [else (oops "observation not boolean: ~s" r)])])
    (when (env? "DISEGNO_LOGS") (report-observation ch b))
    b))

(define (run entry)
  (parameterize ([observe observe-live] [entry-name entry])
    (guard (e [(exec-error e) => (lambda (x)                ; even without logs: which step, and where
                                   (let ([cmd (cdr (assoc "cmd" x))])
                                     ;; a step that is not one of our with-execs (a Dockerfile RUN) has no
                                     ;; stream and no item: in the report the proof is the error's last lines
                                     (release!) (print-waiting)
                                     (when (env? "DISEGNO_LOGS")
                                       (for-each (lambda (l) (printf "  │ ~a\n" l))
                                         (last-lines (lines (cond [(assoc "stdout" x) => cdr] [else ""])
                                                            (cond [(assoc "stderr" x) => cdr] [else ""])) 30)))
                                     (step-failed (cmd-pos cmd) (cdr (assoc "exitCode" x)) (show-args cmd))))])
      (dynamic-wind void
        (lambda ()
          (let ([t0 (now-ns)] [done '()])
            (hashtable-clear! secret-memo)
            (set! held #f) (set! waiting (quote ()))
            (parameterize ([run-id (number->string t0)] [fetch-secret fetch-live] [realize-dry #f])
              (realize (entry-value entry) resolve-live
                       (lambda (ch) (log-steps ch) (submit-leaf ch) (set! done (cons ch done)))))
            (when (env? "DISEGNO_LOGS") (summary (reverse done) (- (now-ns) t0)))
            (outcomes (reverse done))))
        (lambda () (release!) (print-waiting) (stop-stream!))))))

(define (exec-error e)                                   ; → the extensions of an EXEC_ERROR, or #f
  (and (irritants-condition? e) (pair? (condition-irritants e))
       (let ([x (car (condition-irritants e))])
         (and (list? x) (equal? (cond [(assoc "_type" x) => cdr] [else #f]) "EXEC_ERROR") x))))

;; ponytail: the step is found from its command; two identical with-execs give the position of either.
(define (cmd-pos cmd)
  (let-values ([(steps poss) (hashtable-entries step-pos)])
    (let loop ([i 0])
      (cond [(= i (vector-length steps)) #f]
            [(equal? (cond [(assq 'args (cdr (vector-ref steps i))) => cadr] [else #f]) cmd) (vector-ref poss i)]
            [else (loop (+ i 1))]))))

;; Dry: one plan per combination of the branches' outcomes, depth first.
;; → list of ((condition-chain . outcome) ...) . events; the events, in order, are
;; (if chain outcome) for observations, (output chain) for outputs, (fails msg) and (otherwise).
(define (all-plans entry)
  (let explore ([prefix '()])
    (let* ([taken '()] [events '()]
           [_ (parameterize ([observe (lambda (ch)
                                        (let ([b (if (< (length taken) (length prefix)) (list-ref prefix (length taken)) #t)])
                                          (set! taken (append taken (list (cons ch b))))
                                          (set! events (cons (list 'if ch b) events))
                                          b))])
                (realize (entry-value entry) resolve-dry
                         (lambda (ch) (set! events (cons (cond [(pair? ch) (list 'output ch)]
                                                               [(string? ch) (list 'fails ch)]
                                                               [else (list 'otherwise)])
                                                         events)))))])
      (cons (cons taken (reverse events))
            (apply append (map (lambda (i) (explore (append (map cdr (list-head taken i)) '(#f))))
                               (reverse (filter (lambda (i) (>= i (length prefix))) (iota (length taken))))))))))
