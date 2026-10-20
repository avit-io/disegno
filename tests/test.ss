;; Controlli: nucleo, type checker, piano (a secco) e, sotto `dagger api with-session`, esecuzione dal vivo.
;; Uso: scheme --script tests/test.ss   (dal vivo: dagger api with-session scheme --script tests/test.ss)
(define root (path-parent (path-parent (car (command-line)))))   ; <root>/tests/test.ss
(define (at-root p) (if (string=? root "") p (string-append root "/" p)))
(load (at-root "src/core.ss"))
(load (at-root "src/types.ss"))
(load (at-root "src/plan.ss"))

(define (contiene? s sub)
  (let ([n (string-length s)] [k (string-length sub)])
    (let loop ([i 0]) (and (<= (+ i k) n) (or (string=? (substring s i (+ i k)) sub) (loop (+ i 1)))))))

;; --- nucleo ---

(define ciao '((container) (from (address "alpine")) (withExec (args ("echo" "ciao"))) (stdout)))
(assert (string=? (plan->graphql ciao)
                  "container { from(address: \"alpine\") { withExec(args: [\"echo\", \"ciao\"]) { stdout } } }"))
(assert (string=? (base64 (string->utf8 "tok:")) "dG9rOg=="))
(assert (string=? (json-string "a\"b\n") "\"a\\\"b\\n\""))
(assert (equal? (json-read "{\"data\": {\"a\": [1, true, null, \"x\\u0041\\n\"]}}")
                '(("data" ("a" 1 #t null "xA\n")))))

;; --- type checker ---

(import! 'prelude)
(for-each import! '(dagger time net files aws git argocd)) ; per i frammenti qui sotto; le ricette importano da sé
;; L'accelerazione è fidata: su numeri piccoli deve coincidere con le clausole unarie.
(for-each
  (lambda (f)
    (for-each
      (lambda (a)
        (for-each
          (lambda (b)
            (let* ([t (fold-left (lambda (acc x) `(app ,acc (num ,x) e)) `(glob ,(bi (car f))) (list-head (list a b) (cadr f)))]
                   [on (reify 0 (ev '() t))]
                   [off (parameterize ([accelerate #f]) (reify 0 (ev '() t)))])
              (unless (equal? on off) (error 'prova (format "accelerazione di ~a su ~a ~a: ~s invece di ~s" (car f) a b on off)))))
          (iota 7)))
      (iota 7)))
  fast)

(check-file (at-root "cookbook/00-basics.disegno"))
(check-file (at-root "tests/checks.disegno"))                          ; le leggi e le garanzie, come teoremi

(define (rifiuta src atteso)
  (let ([msg (guard (e [(message-condition? e) (condition-message e)]) (check-string src) #f)])
    (unless (and msg (contiene? msg atteso))
      (error 'prova (format "~a: atteso un errore con «~a», ottenuto ~s" src atteso msg)))))

(rifiuta "(claim assurdo ⊥)
(define assurdo assurdo)" "ricorsione non strutturale")
(rifiuta "(claim postulato ⊥)" "claim senza define")
(rifiuta "(data Cattivo (mk (→ Cattivo ⊥)))" "strettamente positiva")
;; Annidato in una lista va bene (List è strettamente positiva nel parametro); sotto una freccia no.
(check-string "(data Rosa (nodo (List Rosa)))")
;; La docstring è l'etichetta di una voce, e le voci senza che chiama la ereditano.
(check-string "(claim con-doc Container)
(define con-doc \"prepara il container\" (pipe (container) (from \"alpine\")))
(claim senza-doc Container)
(define senza-doc (pipe (container) (from \"alpine\")))")
(assert (equal? (voce-doc 'con-doc) "prepara il container"))
(assert (not (voce-doc 'senza-doc)))
(assert (eq? (parameterize ([current-voce 'con-doc]) (enter-voce 'senza-doc)) 'con-doc))
(assert (eq? (parameterize ([current-voce 'senza-doc]) (enter-voce 'con-doc)) 'con-doc))
(rifiuta "(claim due Nat)
(define due 1 2)" "define:")
;; Nel resoconto un segreto letto prima che la voce si apra le va sotto, e due tratti della stessa
;; voce fanno una riga.
(let ([out (with-output-to-string
             (lambda ()
               (secret-line "segreto a letto")
               (report-voce #t 'con-doc "cmd" #f 1000000000 "" "" '())
               (report-voce #t 'con-doc "cmd" #f 1000000000 "" "" '())
               (release!)))])
  (assert (contiene? out "prepara il container"))
  (assert (contiene? out "2.0s"))
  (assert (contiene? out "\n    ↳ segreto a letto\n")))
;; Una domanda, voce che restituisce (Remote Bool), dà la docstring all'osservazione; i suoi passi
;; restano della voce che la pone.
(check-string "(claim c-e-file? (→ String (Remote Bool)))
(define (c-e-file? p) \"c'è il file?\" (probe (pipe (container) (from \"alpine\")) (list \"test\" \"-f\" p)))
(claim chiede (Export Dir))
(define chiede \"controlla\" (unless (c-e-file? \"/x\") (apply (pipe (container) (from \"alpine\")) (list \"true\"))))")
(let ([seen #f])
  (parameterize ([observe (lambda (ch) (set! seen ch) #f)]) (exits resolve-dry 'chiede))
  (let ([exec (list-ref seen (- (length seen) 2))])
    (assert (eq? (hashtable-ref step-question exec #f) 'c-e-file?))
    (assert (eq? (voce-of exec) 'chiede))))
;; TODO, come in Pie: ogni buco della define con il suo contesto e l'obiettivo, risolto dopo
;; l'unificazione; la define è rifiutata.
(let ([m (guard (e [(message-condition? e) (condition-message e)])
           (check-string "(claim piu-zero (Π ((n Nat)) (≡ (+ n 0) n)))
(define (piu-zero n)
  (match n
    (zero TODO)
    ((add1 k) (cong add1 TODO))))") #f)])
  (assert (and m (contiene? m "TODO\n  ──────────\n  (≡ 0 0)")))
  (assert (contiene? m "<stringa>:5:15: TODO\n  k : Nat\n  ──────────\n  (≡ (+ k 0) k)")))
(rifiuta "(claim t Type)
(define t (the TODO Nat))" "non si sa")
(rifiuta "(data Cattivo2 (mk2 (List (→ Cattivo2 ⊥))))" "strettamente positiva")
(rifiuta "(claim tipo-in-tipo Type)
(define tipo-in-tipo Type)" "atteso")
(rifiuta "(data U : Type (u : (→ Type U)))" "livello")
(rifiuta "(claim pred (→ Nat Nat))
(define (pred n)
  (match n
    ((add1 k) k)))" "manca il caso")
(rifiuta "(claim scegli (→ (Either A B) (→ A C) (→ B C) C))
(define (scegli n f _)
  (match n
    ((left a) (f a))))" "manca il caso (scegli (right _) _ _)")   ; come una chiamata, senza metavariabili
(rifiuta "(claim giro (→ Nat Nat))
(define (giro n) (giro n))" "ricorsione non strutturale")
;; match su un valore calcolato: una define ausiliaria chiusa sul contesto. Calcola nelle prove;
;; copre i casi; non nasconde una chiamata alla define in corso.
(check-string "(claim mx-neg (→ Bool Bool))
(define (mx-neg b) (match b (true false) (false true)))
(claim mx-zero? (→ Nat Bool Bool))
(define (mx-zero? n b)
  (let ((m (mx-neg b)))
    (match* (n m)
      ((zero true) true)
      ((_ _) false))))
(claim mx-prova (≡ (mx-zero? 0 false) true))
(define mx-prova refl)")
(rifiuta "(claim mx-manca (→ Bool Bool))
(define (mx-manca b) (match (mx-neg b) (true true)))" "manca il caso")
(rifiuta "(claim mx-giro (→ Nat Nat))
(define (mx-giro n) (match (mx-neg true) (true (mx-giro n)) (false 0)))" "non può richiamare mx-giro")
(rifiuta "(claim mx-libero Type)
(define mx-libero (≡ (match true (true false) (false true)) false))" "annotalo con the")
(rifiuta "(claim falso (≡ 1 2))
(define falso refl)" "atteso")
(rifiuta "(claim testa-vuota (→ (Vec A 0) A))
(define (testa-vuota nil) nil)" "atteso")
(rifiuta "(extern bugia : ⊥ boh)" "riservato alla libreria standard")
(rifiuta "(claim furto Dir)
(define furto (%host-dir \"/etc\"))" "riservato al nucleo")
(rifiuta "(claim diverse (≡ \"a\" \"b\"))
(define diverse refl)" "atteso")
(parameterize ([privileged #t])
  (rifiuta "(extern mente : (→ Dir ⊥) Directory.boh)" "tipo opaco")
  (rifiuta "(extern osserva : (→ Dir String) Directory.name)" "tipo opaco"))

;; --- piano ---

(define dir (format "~a/disegno-prova" (or (getenv "TMPDIR") "/tmp")))
(check-string (format "
(claim gen-config (→ Dir Dir))
(define (gen-config src) (with-file src /config/app.toml \"porta = 8080\\n\"))

(claim main (Π ((src (Host ~s))) (Export Dir)))
(define (main src) (replace ~s (put (with-file empty /LEGGIMI \"ciao\\n\") /cfg (gen-config src))))"
  (string-append dir "/in") (string-append dir "/out")))

(define secco (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch))))))
(assert (contiene? secco "directory { withNewFile(path: \"/LEGGIMI\", contents: \"ciao\\n\", permissions: 420) { withDirectory(path: \"/cfg\", source: \"<host { directory(path:"))
(assert (contiene? secco "withNewFile(path: \\\"/config/app.toml\\\""))
(assert (contiene? secco "} }>\") { export(path:"))
(assert (contiene? secco "wipe: true"))

;; Container: la directory dell'host entra nel container, un comando la elabora, il risultato esce.
(check-string (format "
(claim costruisci (Π ((src (Host ~s))) (Export Dir)))
(define (costruisci src)
  (replace ~s
           (pipe (container)
                 (from \"alpine\")
                 (with-dir /w src)
                 (with-workdir /w)
                 (with-exec (list \"sh\" \"-c\" \"cat dati.txt dati.txt > doppio.txt\"))
                 (dir-of /w))))"
  (string-append dir "/in") (string-append dir "/out2")))
(define secco2 (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch))) 'costruisci)))
(assert (contiene? secco2 "container { from(address: \"alpine\") { withDirectory(path: \"/w\", source: \"<host"))
(assert (contiene? secco2 "withExec(args: [\"sh\", \"-c\", \"cat dati.txt dati.txt > doppio.txt\"]) { directory(path: \"/w\")"))
(rifiuta "(claim mista (List String))
(define mista (list \"a\" 1))" "atteso")
(rifiuta "(claim pipe Dir)
(define pipe empty)" "parola riservata")
(check-string "(claim immagini (≡ (images (pipe (container) (from \"a\") (with-dir /w (dir-of (from container \"b\") root))))
                   (list \"a\" \"b\")))
(define immagini auto)")
(rifiuta "(claim dev-pinnate (All pinned? (images (from container \"alpine\"))))
(define dev-pinnate auto)" "auto: nessuna prova di (Holds pinned? \"alpine\")")
(rifiuta "(claim falso-branch (All pinned? (images (branch (Directory.exists empty /x) (from container \"a@sha256:4bcff63911fcb4448bd4fdacec207030997caf25e9bea4045fa6c8c44de311d1\") (from container \"b\")))))
(define falso-branch auto)" "auto: nessuna prova di")
(rifiuta "(claim sotto App)
(define sotto (app \"api\" prod 2 auto))" "auto: la proposizione si riduce a ⊥")
(rifiuta "(claim falso-auto (≡ (+ 1 1) 3))
(define falso-auto auto)" "atteso")
(check-string "(claim nome-api (≡ (App.name api) \"api\"))
(define nome-api auto)")
(check-string "(claim raddoppia (→ Nat Nat))
(define (raddoppia n) (+ n n))
(claim otto (≡ (pipe 2 raddoppia raddoppia) 8))
(define otto refl)")

;; branch: la condizione è un test nel container; i due rami sono entrambi nel piano.
(check-string (format "
(claim prova-in (→ Dir String Container))
(define (prova-in src file) (pipe (container) (from \"alpine\") (with-dir /w src) (try-exec (list \"test\" \"-f\" file))))

(claim esito (→ (Remote Bool) Dir))
(define (esito c) (branch c (with-file empty /esito \"passa\\n\") (with-file empty /esito \"fallisce\\n\")))

(claim verifica (Π ((src (Host ~s))) (Export Dir)))
(define (verifica src)
  (replace ~s (put (esito (passes? (prova-in src \"/w/dati.txt\")))
                   /manca (esito (exists? src /manca.txt)))))"
  (string-append dir "/in") (string-append dir "/out3")))
(define piani (all-plans 'verifica))
(assert (= (length piani) 4))
(assert (contiene? (plan->graphql (car (car (car (car piani)))))
                   "withExec(args: [\"test\", \"-f\", \"/w/dati.txt\"], expect: ANY) { exitCode }"))
(assert (equal? (map (lambda (p) (map cdr (car p))) piani) '((#t #t) (#t #f) (#f #t) (#f #f))))
(rifiuta "(claim confuso (→ (Remote Bool) Dir))
(define (confuso c) (if c empty empty))" "atteso")
(rifiuta "(claim scelta (→ Bool Dir))
(define (scelta b) (branch b empty empty))" "atteso")

;; Il contenuto dei file lo guarda Dagger: osservazioni come passes?, il testo non torna al linguaggio.
(check-string (format "
(claim contenuto (Π ((src (Host ~s))) (Export Dir)))
(define (contenuto src)
  (let ((f (file-of src /dati.txt)))
    (replace ~s (pipe empty
                      (put /include (esito (includes? f \"dati\")))
                      (put /assente (esito (includes? f \"assente\")))
                      (put /regex (esito (matches? f \"^d.t+i$\")))
                      (put /vuoto (esito (empty? f)))
                      (put /uguale (esito (same-content? f f)))))))"
  (string-append dir "/in") (string-append dir "/out4")))
(assert (= (length (all-plans 'contenuto)) 32))

;; Effetti in sequenza: then realizza in ordine, apply è un effetto fuori dalla cache (una
;; variabile nuova a ogni esecuzione, subito prima del comando), skip non fa niente.
(check-string (format "
(claim sequenza (Export Dir))
(define sequenza
  (begin
    (apply (from (container) \"alpine\") (list \"sh\" \"-c\" \"echo effetto\"))
    skip
    (overlay ~s (with-file empty /dopo \"sì\\n\"))))"
  (string-append dir "/out5")))
(let ([es (exits resolve-dry 'sequenza)])
  (assert (= (length es) 2))
  (assert (contiene? (plan->graphql (car es)) "withEnvVariable(name: \"DISEGNO_RUN\", value: \"<esecuzione>-"))
  (assert (contiene? (plan->graphql (car es)) "\") { withExec(args: [\"sh\", \"-c\", \"echo effetto\"]) { exitCode }"))
  (assert (contiene? (plan->graphql (cadr es)) "export(path:")))
;; Fuori dalla cache: due esecuzioni danno a DISEGNO_RUN valori diversi, quindi per Dagger il
;; comando è un altro; la costruzione prima della variabile resta la stessa, e resta in cache.
(let ([a (parameterize ([run-id "1"]) (plan->graphql (car (exits resolve-dry 'sequenza))))]
      [b (parameterize ([run-id "2"]) (plan->graphql (car (exits resolve-dry 'sequenza))))])
  (assert (not (string=? a b)))
  (assert (contiene? a "value: \"1-")) (assert (contiene? b "value: \"2-")))
;; E dentro la stessa esecuzione due comandi freschi identici restano due: valori diversi.
(check-string "(claim due-volte (Export Dir))
(define due-volte
  (begin
    (apply (from (container) \"alpine\") (list \"true\"))
    (apply (from (container) \"alpine\") (list \"true\"))))")
(let ([es (exits resolve-dry (quote due-volte))]) (assert (not (string=? (plan->graphql (car es)) (plan->graphql (cadr es))))))
(rifiuta "(claim dentro Container)
(define dentro (with-dir (from (container) \"a\") /x (overlay \"o\" empty)))" "atteso")

;; Segreti: (Host-secret "NOME") nella firma, letto da una variabile d'ambiente. Il piano nomina la
;; variabile, mai il valore; il container lo riceve con with-secret-variable.
(check-string (format "
(claim segreto (Π ((s (Host-secret \"PATH\"))) (Export Dir)))
(define (segreto s)
  (branch (probe (with-secret-variable (from (container) \"alpine\") \"S\" s) (list \"sh\" \"-c\" \"test -n \\\"$S\\\"\"))
          (overlay ~s (with-file empty /esito \"ricevuto\\n\"))
          (overlay ~s (with-file empty /esito \"vuoto\\n\"))))
(claim segreto-male (Π ((s (Host-secret \"1 X\"))) (Export Dir)))
(define (segreto-male s) skip)"
  (string-append dir "/out6") (string-append dir "/out6")))
(let ([p (plan->graphql (cadr (car (cdr (car (all-plans 'segreto))))))])
  (assert (contiene? p "withSecretVariable(name: \"S\", secret: \"<secret(uri: \\\"env://PATH\\\")>\")"))
  (assert (not (contiene? p (getenv "PATH")))))
(assert (contiene? (guard (e [#t (condition-message e)]) (all-plans 'segreto-male) "") "non è il nome di una variabile d'ambiente"))
(rifiuta "(claim leggi String)
(define leggi (Query.secret \"env://HOME\"))" "nome sconosciuto")

;; re?: la corrispondenza è con tutta la stringa; termina anche sui pattern che ripetono il vuoto.
(for-each (lambda (c) (unless (eq? (re? (car c) (cadr c)) (caddr c))
                        (error 'prova (format "re? ~s ~s: atteso ~a" (car c) (cadr c) (caddr c)))))
  '(("abc" "abc" #t) ("abc" "abcd" #f) ("a.c" "axc" #t) ("[a-z]+" "ciao" #t) ("[a-z]+" "Ciao" #f)
    ("[^0-9]*" "abc" #t) ("[^0-9]*" "a1" #f) ("\\d{3}" "123" #t) ("\\d{3}" "12" #f) ("a{2,}" "aaaa" #t)
    ("a{2,3}" "aaaa" #f) ("(ab|cd)+" "abcdab" #t) ("(ab|cd)+" "abc" #f) ("colou?r" "color" #t)
    ("\\w+@\\w+\\.it" "x_1@dominio.it" #t) ("(a*)*" "aaaa" #t) ("(a*)*b" "aaaa" #f) ("(a?){3}" "" #t)
    ("[a-z0-9][a-z0-9.-]{1,61}[a-z0-9]" "my-bucket.logs" #t) ("[a-z0-9][a-z0-9.-]{1,61}[a-z0-9]" "-bucket" #f)
    ("a]" "a]" #t) ("" "" #t) ("" "x" #f)))
(for-each (lambda (p) (assert (guard (e [(message-condition? e) (contiene? (condition-message e) "malformata")]) (re? p "x") #f)))
          '("(" "a)" "[a" "*a" "a{2" "a{3,1}" "[z-a]"))
(check-string "(claim logs-bucket Bucket)
(define logs-bucket \"my-app.logs\")")
(rifiuta "(claim bucket-male Bucket)
(define bucket-male \"My_Bucket\")" "«My_Bucket» non è un Bucket valido")

;; AWS: la CLI fissata, con le credenziali come segreti; dal vivo risponde, senza toccare AWS.
(check-string (format "
(claim cli-aws (Π ((s (Host-secret \"PATH\"))) (Export Dir)))
(define (cli-aws s)
  (branch (probe (cli (aws s s \"eu-west-1\" cloud)) (list \"sh\" \"-c\" \"aws --version && test -n \\\"$AWS_ACCESS_KEY_ID\\\" && test \\\"$AWS_DEFAULT_REGION\\\" = eu-west-1\"))
          (overlay ~s (with-file empty /esito \"risponde\\n\"))
          (overlay ~s (with-file empty /esito \"no\\n\"))))"
  (string-append dir "/out7") (string-append dir "/out7")))
(rifiuta "(claim r Region)
(define r \"eu-west-9\")" "«eu-west-9» non è un Region valido")

;; LocalStack come service: il Parameter Store vero, emulato. Si scrive, poi si chiede; il service
;; è lo stesso per tutta la sessione. Dal vivo solo con DISEGNO_TEST_KEY (la shell lo esporta).
(check-string (format "
(claim esito-ls (→ String (Export Dir)))
(define (esito-ls t) (overlay ~s (with-file empty /esito t)))
(claim con-localstack (Π ((k (Host-secret \"DISEGNO_TEST_KEY\"))) (Export Dir)))
(define (con-localstack k)
  (begin
    (start localstack)
    (let ((a (aws k k \"eu-west-1\" (emulated localstack))))
      (begin
        (put-parameter a /app/test/porta \"5432\")
        (put-secure-parameter a /app/test/password k)
        (branch (parameter-is? a /app/test/porta \"5432\")
                (branch (parameter-is? a /app/test/porta \"9999\")
                        (esito-ls \"confonde i valori\\n\")
                        (branch (parameter-exists? a /app/test/password)
                                (esito-ls \"scritto\\n\")
                                (esito-ls \"manca la password\\n\")))
                (esito-ls \"porta non scritta\\n\"))))))"
  (string-append dir "/out8")))
(assert (= (length (all-plans 'con-localstack)) 4))
(check-string (format "
(claim esito-s3 (→ String (Export Dir)))
(define (esito-s3 t) (overlay ~s (with-file empty /esito t)))
(claim bucket-prova Bucket)
(define bucket-prova \"prova-disegno\")
(claim con-s3 (Π ((k (Host-secret \"DISEGNO_TEST_KEY\"))) (Export Dir)))
(define (con-s3 k)
  (begin
    (start localstack)
    (let ((a (aws k k \"eu-west-1\" (emulated localstack))))
      (begin
        (make-bucket a bucket-prova)
        (s3-sync a (with-file empty /index.html \"<h1>ciao</h1>\\n\") bucket-prova /site)
        (branch (s3-includes? a bucket-prova /site/index.html \"ciao\")
                (branch (s3-exists? a bucket-prova /site/manca.html)
                        (esito-s3 \"trova ciò che non c'è\\n\")
                        (esito-s3 \"pubblicato\\n\"))
                (esito-s3 \"pagina assente\\n\"))))))"
  (string-append dir "/out10")))
;; Parametri del piano: (Host-env "NOME" "default"), letti dall'ambiente quando si costruisce il
;; piano. Decidono anche gli if: il piano è una funzione dei parametri.
(check-string (format "
(claim param (Π ((t (Host-env \"DISEGNO_PROVA_TAG\" \"1.0\")) (k (Host-env \"DISEGNO_PROVA_TIPO\" \"release\"))) (Export Dir)))
(define (param t k)
  (if (same? k \"rollback\")
      (overlay ~s (with-file empty /rollback t))
      (overlay ~s (with-file empty /release t))))
(claim param-male (Π ((t (Host-env \"1 X\" \"\"))) (Export Dir)))
(define (param-male t) skip)"
  (string-append dir "/out12") (string-append dir "/out12")))
(let ([p (lambda () (plan->graphql (plan resolve-dry 'param)))])
  (assert (contiene? (p) "withNewFile(path: \"/release\", contents: \"1.0\""))
  (putenv "DISEGNO_PROVA_TIPO" "rollback") (putenv "DISEGNO_PROVA_TAG" "10.0.42")
  (assert (contiene? (p) "withNewFile(path: \"/rollback\", contents: \"10.0.42\""))
  (putenv "DISEGNO_PROVA_TIPO" "") (putenv "DISEGNO_PROVA_TAG" ""))   ; vuota vale come assente
(assert (contiene? (guard (e [#t (condition-message e)]) (plan resolve-dry 'param-male) "") "non è il nome di una variabile d'ambiente"))
;; (Host-choice "NOME" Tipo default): il costruttore con quel nome; un nome sconosciuto ferma il
;; piano. (fail "msg"): a secco un evento del piano, dal vivo l'errore.
(check-string (format "
(data Amb (sviluppo) (produzione))
(claim per-amb (Π ((a (Host-choice \"DISEGNO_PROVA_AMB\" Amb sviluppo))) (Export Dir)))
(define (per-amb a)
  (match a
    (sviluppo (overlay ~s (with-file empty /sviluppo \"\")))
    (produzione (fail \"niente prod da qui\"))))
(claim scelta-male (Π ((a (Host-choice \"DISEGNO_PROVA_AMB\" Nat zero))) (Export Dir)))
(define (scelta-male a) skip)"
  (string-append dir "/out12")))
(assert (contiene? (plan->graphql (plan resolve-dry 'per-amb)) "/sviluppo"))
(putenv "DISEGNO_PROVA_AMB" "produzione")
(assert (equal? (cdr (car (all-plans 'per-amb))) '((fallisce "niente prod da qui"))))
(putenv "DISEGNO_PROVA_AMB" "collaudo")
(assert (contiene? (guard (e [#t (condition-message e)]) (plan resolve-dry 'per-amb) "") "«collaudo» non è uno tra sviluppo, produzione"))
(assert (contiene? (guard (e [#t (condition-message e)]) (plan resolve-dry 'scelta-male) "") "soli costruttori senza argomenti"))
(putenv "DISEGNO_PROVA_AMB" "")
(check-string "(claim amb-nome (≡ (Amb.name produzione) \"produzione\"))
(define amb-nome refl)")   ; D.name, l'inverso di Host-choice, generato con il data
;; Un valore bloccato (qui le credenziali lette da Secrets Manager) ricorda la voce in cui è nato,
;; e la riprende quando il runner lo sblocca: i passi di ECR restano di lavora, non di main.
(check-string "(import aws delivery)
(claim conto (→ Bool Account))
(define (conto b) (match b (true \"111111111111\") (false \"222222222222\")))
(claim altro-aws (→ Aws Aws))
(define (altro-aws boot) (aws (secrets-manager-key-first boot (list \"a\") \"username\" \"u\") (secrets-manager-key-first boot (list \"a\") \"password\" \"p\") \"eu-west-1\" cloud))
(claim lavora (→ Aws Bool (Export Dir)))
(define (lavora boot b) \"pubblica\"
  (let ((reg (ecr (altro-aws boot) (conto b))))
    (unless (Registry.has? reg \"repo\" \"tag\") (Registry.push reg (pipe (container) (from \"alpine\")) \"repo\" \"tag\"))))
(claim etichettato (Π ((id (Host-secret \"AWS_ACCESS_KEY_ID\")) (key (Host-secret \"AWS_SECRET_ACCESS_KEY\")) (s (Host-env \"DISEGNO_PROVA_S\" \"x\"))) (Export Dir)))
(define (etichettato id key s) (lavora (aws id key \"eu-west-1\" cloud) (same? s \"x\")))")
(assert (equal? (map (lambda (ch) (voce-of (last-of (filter (lambda (s) (eq? (car s) 'withExec)) ch))))
                     (parameterize ([observe (lambda (ch) #f)]) (exits resolve-dry 'etichettato)))
                '(lavora lavora)))

;; otherwise: se a fallisce si realizza b, poi si fallisce lo stesso. A secco il piano mostra b
;; dopo il segno «se qualcosa prima fallisce». Per Before, b conta come se a fosse fallito subito.
(check-string (format "
(claim con-riserva (Export Dir))
(define con-riserva
  (otherwise (begin
               (overlay ~s (with-file empty /prima \"sì\\n\"))
               (apply (from (container) \"alpine\") (list \"sh\" \"-c\" \"exit 3\")))
             (overlay ~s (with-file empty /riserva \"sì\\n\"))))
(claim rilascio-o-report (→ Dir (Export Dir)))
(define (rilascio-o-report src)
  (otherwise (when (passes? (try-exec (with-dir (from (container) \"alpine\") /w src) (list \"true\")))
               (apply (from (container) \"alpine\") (list \"echo\" \"deploy\")))
             (overlay \"report\" (with-file empty /fallito \"sì\\n\"))))
(claim deploy-protetto (Π ((src Dir)) (Before test? apply? (rilascio-o-report src))))
(define (deploy-protetto src) auto)"
  (string-append dir "/out13") (string-append dir "/out13")))
(assert (equal? (map car (cdr (car (all-plans 'con-riserva)))) '(uscita uscita altrimenti uscita)))
;; Un apply come riserva non è protetto dal test: Before lo vede, perché b conta da solo.
(rifiuta "(claim riserva-scoperta (Π ((src Dir)) (Before test? apply? (otherwise (rilascio-o-report src) (apply (from (container) \"alpine\") (list \"echo\" \"report\"))))))
(define (riserva-scoperta src) auto)" "auto")

;; Segreti letti a esecuzione: Secrets Manager su LocalStack. Il segreto si crea (qui, in chiaro:
;; è un test), poi un container lo riceve da secrets-manager-key e lo confronta. Il piano del
;; consumatore mostra il comando che lo legge, mai il valore.
(check-string (format "
(claim esito-sm (→ String (Export Dir)))
(define (esito-sm t) (overlay ~s (with-file empty /esito t)))
(claim con-segreti (Π ((k (Host-secret \"DISEGNO_TEST_KEY\"))) (Export Dir)))
(define (con-segreti k)
  (begin
    (start localstack)
    (let ((a (aws k k \"eu-west-1\" (emulated localstack))))
      (begin
        (apply (cli a) (list \"aws\" \"secretsmanager\" \"create-secret\" \"--name\" \"cicd/test/argocd\"
                             \"--secret-string\" \"{\\\"host\\\":\\\"argocd.example\\\",\\\"token\\\":\\\"t0k\\\"}\"))
        (apply (cli a) (list \"aws\" \"secretsmanager\" \"create-secret\" \"--name\" \"cicd/test/chiave\"
                             \"--secret-binary\" \"dW5vCmR1ZQo=\"))
        (branch (probe (pipe (from (container) \"alpine\")
                             (with-secret-variable \"T\" (secrets-manager-key a \"cicd/test/argocd\" \"token\"))
                             (with-secret-variable \"K\" (secrets-manager-first a (list \"cicd/test/assente\" \"cicd/test/chiave\") \"chiave\"))
                             ;; il segreto c'è ma la chiave no: vale il default, e nient'altro
                             (with-secret-variable \"D\" (secrets-manager-key-first-or a (list \"cicd/test/argocd\") \"server\" \"riserva\" \"argocd-server\")))
                       (list \"sh\" \"-c\" \"test \\\"$T\\\" = t0k && test \\\"$K\\\" = \\\"$(printf 'uno\\\\ndue')\\\" && test \\\"$D\\\" = riserva\"))
                (esito-sm \"ricevuto\\n\")
                (esito-sm \"diverso\\n\"))))))"
  (string-append dir "/out11")))
(let* ([evs (cdr (car (all-plans 'con-segreti)))]
       [obs (plan->graphql (cadr (find (lambda (e) (eq? (car e) 'se)) evs)))])
  (assert (contiene? obs "secretFrom(name: \\\"cicd/test/argocd:token\\\", args: [\\\"sh\\\", \\\"-c\\\""))   ; il nome e il comando, dentro la stringa GraphQL
  (assert (contiene? obs "\\\"cicd/test/argocd\\\", \\\"token\\\"]"))
  (assert (not (contiene? obs "argocd.example"))))                   ; il valore del segreto non è nel piano

;; delivery: Registry, Gitops e Deployer, con le loro implementazioni. Un registro e un server git
;; come service, per provare push, «c'è?», clone, kustomize, commit e push senza servizi esterni.
(check-string (format "
(claim esito-d (→ Segment String (Export Dir)))
(define (esito-d p t) (overlay ~s (with-file empty (/ root p) t)))
(claim immagine-prova Container)
(define immagine-prova (pipe (container) (from \"busybox@sha256:bdf57e528e45e4433820e045b29b4597825a1c9e38353532d90a01445013f82e\")))
(claim con-registro (Export Dir))
(define con-registro
  (begin
    (start registry-service)
    (Registry.push (local-registry registry-service) immagine-prova \"prova/app\" \"v1\")
    (branch (Registry.has? (local-registry registry-service) \"prova/app\" \"v1\")
            (esito-d \"registro\" \"pubblicata\\n\")
            (esito-d \"registro\" \"assente\\n\"))))
(claim server-git Service)
(define server-git
  (pipe git-tool
        (with-exec (list \"sh\" \"-c\" \"apk add -q --no-cache git-daemon && git init -q --bare -b main /srv/app.git && git init -q -b main /tmp/w && cd /tmp/w && mkdir -p console/test/app && printf 'resources: []\\\\n' > console/test/app/kustomization.yaml && git add -A && git -c user.name=t -c user.email=t@t commit -qm init && git push -q /srv/app.git main\"))
        (with-exposed-port 9418)
        (with-default-args (list \"git\" \"daemon\" \"--reuseaddr\" \"--export-all\" \"--enable=receive-pack\" \"--base-path=/srv\" \"/srv\"))
        (as-service false)))
(claim repo-prova Gitops)
(define repo-prova (kustomize-gitops \"git://git:9418/app.git\" \"main\" anonymous (through \"git\" server-git) (author \"Disegno\" \"ci@disegno.invalid\")))
(claim con-gitops (Export Dir))
(define con-gitops
  (begin
    (start server-git)
    (Gitops.set-image repo-prova (list \"console/test/app\") \"registry:5000/prova/app:v2\" \"immagine v2\")
    (branch (probe (with-dir immagine-prova /r (clone \"git://git:9418/app.git\" \"main\" anonymous (through \"git\" server-git)))
                   (list \"grep\" \"-q\" \"newTag: v2\" \"/r/console/test/app/kustomization.yaml\"))
            (esito-d \"gitops\" \"aggiornato\\n\")
            (esito-d \"gitops\" \"invariato\\n\"))))
(claim con-argocd (Π ((s (Host-secret \"PATH\"))) (Export Dir)))
(define (con-argocd s)
  (branch (probe (argocd-cli (argocd (public \"argocd.invalid\") (token s) false)) (argocd-args (list \"version\" \"--client\")))
          (esito-d \"argocd\" \"risponde\\n\")
          (esito-d \"argocd\" \"no\\n\")))
(claim rilascio-prova (→ Secret (Export Dir)))
(define (rilascio-prova s)
  (begin
    (Gitops.set-image repo-prova (list \"console/test/app\") \"registry:5000/prova/app:v3\" \"v3\")
    (Deployer.deploy (argocd-deployer (argocd (public \"argocd.invalid\") (token s) false) 300) \"app\")))
(claim sync-dopo-push (Π ((s Secret)) (Precedes (git-command? \"push\") (argocd-command? \"sync\") (rilascio-prova s))))
(define (sync-dopo-push s) auto)"
  (string-append dir "/out14")))
(rifiuta "(claim push-dopo-sync (Π ((s Secret)) (Precedes (argocd-command? \"sync\") (git-command? \"push\") (rilascio-prova s))))
(define (push-dopo-sync s) auto)" "auto")

;; Una build da Dockerfile con un argomento e un segreto per nome: ARG VERSIONE e
;; RUN --mount=type=secret,id=ssh-key li vedono.
(check-string (format "
(claim contesto Dir)
(define contesto (with-file empty /Dockerfile \"FROM busybox@sha256:bdf57e528e45e4433820e045b29b4597825a1c9e38353532d90a01445013f82e\\nARG VERSIONE\\nRUN --mount=type=secret,id=ssh-key mkdir /out && test \\\"$(cat /run/secrets/ssh-key)\\\" = chiave && echo letto $VERSIONE > /out/esito\\n\"))
(claim con-dockerfile (Export Dir))
(define con-dockerfile
  (overlay ~s (dir-of (build-dockerfile contesto \"Dockerfile\" (list (build-arg \"VERSIONE\" \"1.2\"))
                                        (list (secret-from (from (container) \"busybox@sha256:bdf57e528e45e4433820e045b29b4597825a1c9e38353532d90a01445013f82e\") (list \"echo\" \"chiave\") \"ssh-key\")))
                      /out)))"
  (string-append dir "/out15")))

;; Argomenti opzionali promossi: i permessi di un file, i glob di filter, l'entrypoint di un service.
(check-string (format "
(claim d9 Dir)
(define d9 (pipe empty (with-executable /run.sh \"#!/bin/sh\\necho ok\\n\") (with-file /note.txt \"x\\n\")))
(claim filtri (Export Dir))
(define filtri
  (branch (passes? (try-exec (with-dir (from (container) \"alpine\") /w d9) (list \"sh\" \"-c\" \"test -x /w/run.sh && test ! -x /w/note.txt\")))
          (overlay ~s (only d9 (list \"*.sh\")))
          (overlay ~s (with-file empty /errore \"permessi\\n\"))))"
  (string-append dir "/out9") (string-append dir "/out9")))
(let ([p (plan->graphql (cadr (cadr (cdr (car (all-plans 'filtri))))))])
  (assert (contiene? p "withNewFile(path: \"/run.sh\", contents: \"#!/bin/sh\\necho ok\\n\", permissions: 493)"))
  (assert (contiene? p "filter(exclude: [], include: [\"*.sh\"])")))
(assert (contiene? (plan->graphql (chain (ev '() '(glob localstack)) resolve-dry)) "asService(useEntrypoint: true)"))
;; Nel resoconto uno script lungo di una libreria si legge dai suoi argomenti; uno corto resta.
(assert (string=? (show-args (list "sh" "-c" (make-string 130 #\x) "sh" "MODE" "cicd/deploy")) "sh -c … sh MODE cicd/deploy"))
(assert (string=? (show-args (list "sh" "-c" "echo effetto")) "sh -c \"echo effetto\""))

;; Che cosa scrive un piano: solo le put-parameter, non gli altri effetti.
(check-string "(claim scritti (Π ((a Aws)) (≡ (parameters (begin
                                             (put-parameter a /app/x \"1\")
                                             (apply (from (container) \"b\") (list \"echo\"))))
                               (list /app/x))))
(define (scritti a) auto)")
(assert (contiene? (plan->graphql (car (car (car (car (all-plans 'contenuto))))))
                   "withExec(args: [\"grep\", \"-qF\", \"dati\", \"/f\"], expect: ANY) { exitCode }"))

;; Extern generati dallo schema, usati direttamente: Nat e oggetti per ID negli argomenti.
(check-string "
(claim servizio (Π ((src (Host \"/x\"))) (Export Dir)))
(define (servizio src)
  (overlay \"out\" (pipe (Query.git \"https://example.com/r.git\") (GitRepository.branch \"main\") GitRef.tree
                       (put /porta (dir-of (Container.with-exposed-port (container) 8080) root)))))")
(define secco3 (plan->graphql (plan resolve-dry 'servizio)))
(assert (contiene? secco3 "git(url: \"https://example.com/r.git\") { branch(name: \"main\") { tree {"))
(assert (contiene? secco3 "withExposedPort(port: 8080)"))

;; Proprietà d'ordine: valgono per ogni input, perché effects non scende nelle directory.
(check-string "
(claim img (→ Dir Container))
(define (img src) (pipe (container) (from \"alpine\") (with-dir /app src)))
(claim protetto (→ Dir (Export Dir)))
(define (protetto src)
  (branch (passes? (try-exec (from container \"alpine\") (list \"true\")))
          (branch (exists? src /VERSION) (publish (img src) \"r/app:1\") (overlay \"o\" src))
          (overlay \"o\" src)))
(claim ordine-ok (Π ((src Dir)) (Before test? publish? (protetto src))))
(define (ordine-ok src) auto)")
(rifiuta "(claim scoperto (Π ((src Dir)) (Before test? publish? (publish (img src) \"r/app:1\"))))
(define (scoperto src) auto)"
         "si riduce a ⊥")
(rifiuta "(claim finto-test (Π ((src Dir)) (Before test? publish? (branch (exists? src /x) (publish (img src) \"r\") (overlay \"o\" src)))))
(define (finto-test src) auto)"
         "si riduce a ⊥")
(rifiuta "(claim nel-ramo-sbagliato (Π ((src Dir)) (Before test? publish? (branch (passes? (img src)) (overlay \"o\" src) (publish (img src) \"r\")))))
(define (nel-ramo-sbagliato src) auto)"
         "si riduce a ⊥")

;; Nomi corti: il tipo del primo argomento sceglie il metodo; senza metodo è un campo radice.
(check-string "
(claim corto (Π ((src (Host \"/x\"))) (Export Dir)))
(define (corto src)
  (overlay \"out\" (pipe (container) (from \"alpine\") (with-mounted-cache /c (cache-volume \"k\"))
                       (directory root) (with-new-file /a \"b\" 420) (directory /sub))))")
(define secco4 (plan->graphql (plan resolve-dry 'corto)))
(assert (contiene? secco4 "withMountedCache(path: \"/c\", cache: \"<cacheVolume(key: \\\"k\\\")>\") { directory(path: \"/\") { withNewFile(path: \"/a\", contents: \"b\", permissions: 420) { directory(path: \"/sub\")"))
(rifiuta "(claim sbagliato Dir)
(define sbagliato (with-exec empty (list \"x\")))" "with-exec non esiste per")
(rifiuta "(claim pinna Dir)
(define pinna (Query.cache-volume \"k\"))" "nome sconosciuto")

;; Valori raffinati e percorsi: il letterale resta, il tipo cambia; i punti non si sommano.
(rifiuta "(claim c1 Container)
(define c1 (from container \"Golang:1.25\"))" "«Golang:1.25» non è un Image valido")
(rifiuta "(claim c2 Container)
(define c2 (from container \"golang:1.25@sha256:abc\"))" "non è un Image valido")
(rifiuta "(claim c3 Dir)
(define c3 (with-file empty /a/../b \"x\"))" "«..» non è un Segment valido")
(rifiuta "(claim c4 Abs)
(define c4 (/ /out /bin))" "atteso Segment, trovato Abs")
(rifiuta "(claim c5 (⊑ /out /out/bin))
(define c5 auto)" "auto: nessuna prova di (⊑ /out /out/bin)")
(check-string "(claim c6 Container)
(define c6 (from container \"ghcr.io/dagger/engine:v0.21.10\"))
(claim c7 (⊑ (/ /out \"hello\") /out))
(define c7 auto)
(claim c8 (≡ (let ((o /out)
                   (b (/ o \"x\"))) b) /out/x))
(define c8 auto)")

;; Lo spazio affine dei percorsi: la differenza esiste solo con la prova di contenimento.
(check-string "
(claim vettore (≡ (⊖ /out/bin/hello /out auto) \"bin/hello\"))
(define vettore auto)
(claim somma (≡ (⊕ /out \"bin/hello\") /out/bin/hello))
(define somma auto)
(claim legge-ereditata (≡ (⊕ /out (⊖ /out/bin /out auto)) /out/bin))
(define legge-ereditata (Affine.law percorsi /out/bin /out auto))")
(rifiuta "(claim storto Rel)
(define storto (⊖ /out /src auto))" "auto: nessuna prova di (⊑ /out /src)")
(rifiuta "(claim punti Abs)
(define punti (⊕ /out /bin))" "atteso Rel, trovato Abs")

;; Regioni: montaggi sovrapposti nella stessa catena sono rifiutati; in catene diverse no.
(check-string "
(claim disgiunti (⋔ /src /go/pkg/mod))
(define disgiunti auto)
(claim due-catene (Disjoint-mounts (pipe (container) (with-dir /w (dir-of (pipe (container) (with-dir /w empty)) /w)))))
(define due-catene auto)")
(rifiuta "(claim annidati (⋔ /src /src/cache))
(define annidati auto)" "auto: nessuna prova di (⋔ /src /src/cache)")
(rifiuta "(claim sovrapposti (Π ((src Dir)) (Disjoint-mounts (pipe (container) (with-dir /src src) (with-mounted-cache /src/cache (cache-volume \"c\"))))))
(define (sovrapposti src) auto)"
         "auto: nessuna prova")

;; Pattern assurdi: solo dove nessun costruttore è possibile; non sono una scappatoia.
(rifiuta "(claim finto-assurdo (¬ (≡ 0 0)))
(define (finto-assurdo n)
  (match n
    (())))" "() non è assurdo: refl è possibile")
(rifiuta "(claim finto-assurdo2 (¬ (⊑ /out/x /out)))
(define (finto-assurdo2 n)
  (match n
    ((⊑-step ()))))" "() non è assurdo")
(rifiuta "(claim falso-diretto ⊥)
(define (falso-diretto n)
  (match n
    (())))" "troppi pattern")
(rifiuta "(claim vero-negato (¬ (⊑ /out/x /out)))
(define vero-negato auto)" "auto: nessuna refutazione di (⊑ /out/x /out)")

;; Letterali di tempo, indirizzi e porte: malformati o fuori spazio sono errori di tipo.
(rifiuta "(claim t1 Instant)
(define t1 \"2026-13-01\")" "«2026-13-01» non è un Instant valido")
(rifiuta "(claim t2 Duration)
(define t2 \"5x\")" "«5x» non è un Duration valido")
(rifiuta "(claim t3 Ip)
(define t3 \"10.0.0.256\")" "«10.0.0.256» non è un Ip valido")
(rifiuta "(claim t4 Cidr)
(define t4 \"10.0.0.1/24\")" "«10.0.0.1/24» non è un Cidr valido")
(rifiuta "(claim t5 Container)
(define t5 (with-exposed-port (container) 70000))" "«70000» non è un Port valido")
(rifiuta "(claim t6 Instant)
(define t6 (⊕ inizio fine))" "atteso Duration, trovato Instant")
(check-string "(claim ultimo Ip)
(define ultimo \"255.255.255.255\")")
(rifiuta "(claim oltre Ip)
(define oltre (⊕ ultimo 1 auto))" "si riduce a ⊥")      ; l'overflow è escluso

;; Il cookbook: ogni ricetta è un programma a sé, verificato in un processo separato con
;; check (tipi e teoremi) e, se ha un main, plan (il piano a secco). Mai run: la 03 pubblica.
;; Anche i capitoli del libro (book/) e le soluzioni degli esercizi (book/solutions/) sono programmi verificati.
(for-each
  (lambda (r)
    (let* ([path (at-root r)]
           [mode (if (contiene? (call-with-input-file path get-string-all) "(claim main ") "plan" "check")])
      (unless (zero? (system (format "scheme --script ~a ~a ~a >/dev/null" (at-root "src/main.ss") mode path)))
        (error 'prova (format "~a non passa (~a)" r mode)))))
  (apply append
         (map (lambda (dir)
                (map (lambda (f) (string-append dir "/" f))
                     (sort string<? (filter (lambda (f) (let ([n (string-length f)]) (and (> n 8) (string=? (substring f (- n 8) n) ".disegno"))))
                                            (directory-list (at-root dir))))))
              '("cookbook" "book" "book/solutions"))))

;; Quando auto fallisce su una congiunzione, il messaggio indica la parte che non vale.
(rifiuta "(claim subnet-sovrapposte (Disjoint-subnets (list \"10.0.1.0/24\" \"10.0.2.0/24\" \"10.0.1.128/25\")))
(define subnet-sovrapposte auto)"
         "auto: nessuna prova di (Cidr-apart \"10.0.1.0/24\" \"10.0.1.128/25\")")
(rifiuta "(claim porte-ripetute (Distinct-ports (pipe (container) (with-exposed-port 80) (with-exposed-port 443) (with-exposed-port 80))))
(define porte-ripetute auto)"
         "auto: nessuna prova di (port≠ 80 80)")
(rifiuta "(claim montaggi-annidati (Disjoint-mounts (pipe (container) (with-dir /src empty) (with-mounted-cache /src/cache (cache-volume \"c\")))))
(define montaggi-annidati auto)"
         "auto: nessuna prova di (⋔ /src/cache /src)")
;; Le posizioni: file:riga:colonna dell'espressione più vicina.
(rifiuta "(claim ok Nat)
(define ok 1)
(claim male Abs)
(define male (⊕ /out /bin))" "<stringa>:4:14: /bin: atteso Rel, trovato Abs")
;; Un errore non ferma il file; chi usa un nome la cui firma è sbagliata non aggiunge errori.
(rifiuta "(claim a Nat)
(define a zz)
(claim b Bool)
(define b 3)" "<stringa>:4:1: 3: atteso Bool")
;; import: solo i moduli di lib/, per nome; un percorso non passa.
(rifiuta "(import ../tests/checks)" "non è il nome di un modulo")
(rifiuta "(import nessuno)" "il modulo nessuno non esiste")
;; builtin: solo nella libreria, chiavi chiuse, una volta, del genere giusto.
(rifiuta "(builtin nat Nat)" "builtin è riservato alla libreria standard")
(parameterize ([privileged #t])
  (rifiuta "(builtin intero Nat)" "chiave sconosciuta intero")
  (rifiuta "(builtin nat Bool)" "nat è già legato a Nat"))
;; Nelle firme si generalizzano solo i nomi da variabile: Porta non è un tipo implicito.
(rifiuta "(claim f (→ Porta Nat))
(define (f _) 0)" "nome sconosciuto: Porta")
(assert (equal? (guard (e [#t (condition-message e)]) (check-string "(claim f (→ Nat \"x\"))
(define (f _) 0)
(claim g Nat)
(define g (f 1))") #f)
                "<stringa>:1:10: \"x\" non è un tipo"))

;; L'LSP: una sessione registrata (initialize, apertura con un errore, correzione, salvataggio,
;; shutdown) letta dal server da stdin; la diagnostica compare e poi si svuota.
(let* ([frame (lambda (v) (let ([b (string->utf8 (json->string v))])
                            (string-append (format "Content-Length: ~a\r\n\r\n" (bytevector-length b)) (utf8->string b))))]
       [uri "file:///tmp/prova-lsp.disegno"]
       [in "/tmp/disegno-lsp-in"] [out "/tmp/disegno-lsp-out"]
       [msg (lambda (method params . id) `(("jsonrpc" . "2.0") ,@(if (null? id) '() `(("id" . ,(car id)))) ("method" . ,method) ("params" . ,params)))])
  (call-with-output-file in
    (lambda (p)
      (for-each (lambda (m) (put-string p (frame m)))
        (list (msg "initialize" '(("capabilities" . (("x" . 1)))) 1)
              (msg "textDocument/didOpen" `(("textDocument" . (("uri" . ,uri) ("text" . "(import paths)
(claim male Abs)
(define male (⊕ /out /bin))
(claim peggio Nat)
(define peggio \"x\")
")))))
              (msg "textDocument/didChange" `(("textDocument" . (("uri" . ,uri))) ("contentChanges" . ,(vector '(("text" . "(import paths)
(claim bene Abs)
(define bene (⊕ /out \"bin\"))
(claim r (≡ 1 1))
(define r refl)
"))))))
              (msg "textDocument/didSave" `(("textDocument" . (("uri" . ,uri)))))
              (msg "textDocument/hover" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 2) ("character" . 14)))) 3)
              (msg "textDocument/definition" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 4) ("character" . 11)))) 4)
              (msg "textDocument/definition" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 2) ("character" . 9)))) 5)
              (msg "textDocument/documentSymbol" `(("textDocument" . (("uri" . ,uri)))) 6)
              (msg "shutdown" '(("x" . 1)) 2)
              (msg "exit" '(("x" . 1)))))) 'replace)
  (system (format "scheme --script ~a lsp < ~a > ~a" (at-root "src/main.ss") in out))
  (let ([r (call-with-input-file out get-string-all)])
    (assert (contiene? r "\"capabilities\""))
    (assert (contiene? r "\"range\":{\"start\":{\"line\":2,\"character\":13}"))
    (assert (contiene? r "\"message\":\"/bin: atteso Rel, trovato Abs\""))
    (assert (contiene? r "\"range\":{\"start\":{\"line\":4,\"character\":0}"))   ; anche il secondo errore
    (assert (contiene? r "\"id\":4,\"result\":[{\"uri\":\"file:///"))         ; refl: nella libreria standard
    (assert (contiene? r "lib/prelude.disegno\",\"range\":{\"start\":{\"line\":6,"))
    (assert (contiene? r (format "\"id\":5,\"result\":[{\"uri\":\"~a\",\"range\":{\"start\":{\"line\":2,\"character\":0}" uri)))   ; bene: la sua define
    (assert (contiene? r "\"name\":\"bene\",\"kind\":12"))
    (assert (contiene? r "\"name\":\"r\",\"kind\":12"))
    (assert (contiene? r "\"diagnostics\":[]"))
    (assert (contiene? r "\"id\":3,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```disegno\\nAbs.⊕ : (→ Abs Rel Abs)\\n"))   ; e le altre varianti di ⊕
    (assert (contiene? r "\"id\":2,\"result\":null"))))

;; Nei pattern un simbolo è un costruttore solo se lo è del tipo atteso: step, port, root…
;; restano variabili dove il tipo è un altro. La copertura usa la stessa risoluzione.
(check-string "
(claim somma-step (→ Nat (→ Nat Nat) Nat))
(define (somma-step port n)
  (match n
    (step (step port))))
(claim usa-step (≡ (somma-step 2 add1) 3))
(define usa-step auto)")
(rifiuta "(claim manca-step (→ Rel Nat))
(define (manca-step n)
  (match n
    (here 0)))" "manca il caso")

;; Il flusso dei log riordina per istante: un pacchetto di stderr consegnato tardi va al suo posto.
(let ([p (open-output-string)])
  (define (record t s)
    `(("timeUnixNano" . ,(number->string t)) ("body" ("stringValue" . ,s)) ("attributes" (("key" . "stdio.stream")))))
  (set! log-port p)
  (for-each (lambda (t s) (on-log (record t s))) '(100 300 200) '("A\n" "C\n" "B\n"))
  (flush! (- (now-ns) window))                          ; appena arrivate: aspettano
  (assert (string=? (get-output-string p) ""))
  (flush! +inf.0)
  (assert (string=? (get-output-string p) "A\nB\nC\n"))
  (set! log-port #f))

;; --- dal vivo ---















(define (esegui entry)                                    ; → (messaggio . output) di run entry
  (let* ([msg #f]
         [out (with-output-to-string
                (lambda () (set! msg (guard (e [(message-condition? e) (condition-message e)]) (run entry) #f))))])
    (cons msg out)))

(when (getenv "DAGGER_SESSION_PORT")
  (system (format "rm -rf ~a && mkdir -p ~a/in && echo dati > ~a/in/dati.txt" dir dir dir))
  (submit-leaf (plan (lambda (ch) (submit-leaf (append ch '((id)))))))
  (for-each (lambda (f) (assert (file-exists? (string-append dir "/out/" f))))
            '("LEGGIMI" "cfg/dati.txt" "cfg/config/app.toml"))
  (submit-leaf (plan (lambda (ch) (submit-leaf (append ch '((id))))) 'costruisci))
  (assert (string=? (call-with-input-file (string-append dir "/out2/doppio.txt") get-string-all) "dati\ndati\n"))
  (run 'verifica)
  (assert (string=? (call-with-input-file (string-append dir "/out3/esito") get-string-all) "passa\n"))
  (assert (string=? (call-with-input-file (string-append dir "/out3/manca/esito") get-string-all) "fallisce\n"))
  (run (quote contenuto))
  (for-each (lambda (p e) (assert (string=? (call-with-input-file (string-append dir "/out4/" p "/esito") get-string-all) e)))
            (quote ("include" "assente" "regex" "vuoto" "uguale")) (quote ("passa\n" "fallisce\n" "passa\n" "fallisce\n" "passa\n")))
  ;; Un passo fallito dice dove sta nel sorgente, con e senza il resoconto (DISEGNO_LOGS, come in
  ;; CI: una riga per voce). Prima senza: Chez non sa togliere una variabile d'ambiente.
  ;; in-diretta ha comandi nuovi a ogni prova, così non è in cache e le righe passano dal flusso.
  (putenv "GITHUB_ACTIONS" "") (putenv "GITLAB_CI" "")       ; il formato neutro, anche in CI
  (let ([n (time-nanosecond (current-time))])
    (check-string (format "(claim rotto (→ (Export Dir)))
(define rotto
  (overlay \"rotto\" (pipe (container) (from \"alpine\")
                         (with-exec (list \"sh\" \"-c\" \"echo A; sleep 0.3; echo B >&2; sleep 0.3; echo C\"))
                         (with-exec (list \"sh\" \"-c\" \"echo male >&2; exit 3\")) (dir-of /tmp))))
(claim prepara Container)
(define prepara \"prepara l'ambiente\" (pipe (container) (from \"alpine\") (with-exec (list \"sh\" \"-c\" \"echo prep~a\"))))
(claim in-diretta (Π ((src (Host ~s))) (Export Dir)))
(define (in-diretta src)
  (overlay \"rotto\" (pipe prepara (with-dir /w src)
                         (with-exec (list \"sh\" \"-c\" \"echo A~a; sleep 0.05; echo B >&2; sleep 0.05; echo C\"))
                         (with-exec (list \"sh\" \"-c\" \"echo male~a >&2; exit 3\")) (dir-of /tmp))))"
                          n (string-append dir "/in") n n))
    (let ([r (esegui 'rotto)])
      (assert (and (car r) (contiene? (car r) "<stringa>:5:26: passo fallito (exit 3)")))
      (assert (string=? (cdr r) "")))
    (putenv "DISEGNO_LOGS" "1")
    ;; Il resoconto: una riga per voce, con i nomi del programma; prepara non vede l'input ed è
    ;; ambiente; in-diretta fallisce, e le ultime righe del passo dicono perché.
    (let* ([r (esegui 'in-diretta)] [msg (car r)] [out (cdr r)])
      (assert (> streamed 0))                                 ; le righe sono arrivate dal flusso
      (assert (contiene? out "✓ prepara l'ambiente  "))
      (assert (contiene? out "✗ in-diretta  <stringa>:12:26  exit 3  "))
      (assert (contiene? out (format "\n      male~a\n" n)))
      (assert (not (contiene? out (format "A~a" n))))         ; la prova di ciò che è andato non si stampa
      (assert (and msg (contiene? msg "<stringa>:12:26: passo fallito (exit 3)"))))
    ;; Un RUN di Dockerfile fallito non è una voce: le sue ultime righe vengono dall'errore.
    (check-string (format "(claim contesto-rotto Dir)
(define contesto-rotto (with-file empty /Dockerfile \"FROM busybox@sha256:bdf57e528e45e4433820e045b29b4597825a1c9e38353532d90a01445013f82e\\nRUN echo docker~a >&2 && exit 4\\n\"))
(claim build-rotta (Export Dir))
(define build-rotta (overlay \"rotto\" (dir-of (build-dockerfile contesto-rotto \"Dockerfile\" (list) (list)) /tmp)))" n))
    (let ([r (esegui 'build-rotta)])
      (assert (contiene? (cdr r) (format "│ docker~a\n" n)))
      (assert (and (car r) (contiene? (car r) "passo fallito (exit 4)"))))
    ;; In CI la prova sta nel gruppo della voce: stdout e stderr intrecciati. Il primo passo ora è
    ;; in cache: il flusso tace, e la prova è combinedOutput.
    (set! logged '())                                         ; un run nuovo, come un processo nuovo
    (putenv "GITHUB_ACTIONS" "true")
    (let ([out (cdr (esegui 'in-diretta))])
      (putenv "GITHUB_ACTIONS" "")
      (assert (contiene? out "::group::✓ prepara l'ambiente  "))
      (assert (contiene? out (format "\"\nA~a\nB\nC\n" n)))
      (assert (contiene? out "::error file=<stringa>,line=12,col=26::passo fallito (exit 3)"))))
  ;; Le uscite vengono nell'ordine di then, e il resoconto mostra l'effetto con il suo comando.
  (let ([r2 (begin (set! logged '()) (esegui 'sequenza))])
    (assert (contiene? (cdr r2) "✓ sequenza    sh -c \"echo effetto\"  "))
    (assert (contiene? (cdr r2) "realizzato in "))
    (assert (contiene? (cdr r2) ": effetto sh -c \"echo effetto\", esportato "))
    (assert (string=? (call-with-input-file (string-append dir "/out5/dopo") get-string-all) "sì\n")))
  ;; Una voce con docstring è una riga sola anche con due effetti (due catene), e la riga finale
  ;; dice l'etichetta, non i comandi.
  (let ([n (time-nanosecond (current-time))])
    (check-string (format "(claim due-passi (Export Dir))
(define due-passi \"fa due cose\"
  (begin (apply (pipe (container) (from \"alpine\")) (list \"sh\" \"-c\" \"echo uno~a\"))
         (apply (pipe (container) (from \"alpine\")) (list \"sh\" \"-c\" \"echo due~a\"))))" n n))
    (set! logged '())
    (let ([out (cdr (esegui 'due-passi))])
      (assert (= 1 (length (filter (lambda (l) (contiene? l "fa due cose  ")) (last-lines out 50)))))
      (assert (contiene? out ": fa due cose\n"))))
  (run 'segreto)
  (assert (string=? (call-with-input-file (string-append dir "/out6/esito") get-string-all) "ricevuto\n"))
  (run 'cli-aws)
  (assert (string=? (call-with-input-file (string-append dir "/out7/esito") get-string-all) "risponde\n"))
  (let ([r (esegui 'con-riserva)])                       ; fallisce, ma prima la riserva
    (assert (and (car r) (contiene? (car r) "passo fallito (exit 3)")))
    (assert (file-exists? (string-append dir "/out13/prima")))
    (assert (file-exists? (string-append dir "/out13/riserva"))))
  (for-each (lambda (e f t) (run e) (assert (string=? (call-with-input-file (string-append dir "/out14/" f) get-string-all) t)))
            '(con-registro con-gitops con-argocd) '("registro" "gitops" "argocd") '("pubblicata\n" "aggiornato\n" "risponde\n"))
  (run 'con-dockerfile)
  (assert (string=? (call-with-input-file (string-append dir "/out15/esito") get-string-all) "letto 1.2\n"))
  (run 'filtri)
  (assert (zero? (system (format "test -x ~a/out9/run.sh" dir))))
  (assert (not (file-exists? (string-append dir "/out9/note.txt"))))
  (when (getenv "DISEGNO_TEST_KEY")
    (run 'con-segreti)
    (assert (string=? (call-with-input-file (string-append dir "/out11/esito") get-string-all) "ricevuto\n"))
    (run 'con-s3)
    (assert (string=? (call-with-input-file (string-append dir "/out10/esito") get-string-all) "pubblicato\n"))
    (run 'con-localstack)
    (assert (string=? (call-with-input-file (string-append dir "/out8/esito") get-string-all) "scritto\n")))
  (system (format "rm -rf ~a" dir))
  (display "dal vivo: ok\n"))
(display "ok\n")
