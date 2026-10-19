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
(for-each import! '(dagger time net files aws))            ; per i frammenti qui sotto; le ricette importano da sé
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

(rifiuta "(def assurdo : ⊥ assurdo)" "ricorsione non strutturale")
(rifiuta "(def postulato : ⊥)" "manca la definizione")
(rifiuta "(data Cattivo [mk (→ Cattivo ⊥)])" "strettamente positiva")
(rifiuta "(def tipo-in-tipo : Type Type)" "atteso")
(rifiuta "(data U : Type [u : (→ Type U)])" "livello")
(rifiuta "(def pred : (→ Nat Nat) [(add1 k)] k)" "manca il caso")
(rifiuta "(def scegli : (→ (Either A B) (→ A C) (→ B C) C) [(left a) f _] (f a))" "manca il caso [(right _) _ _]")   ; come una clausola, senza metavariabili
(rifiuta "(def giro : (→ Nat Nat) [n] (giro n))" "ricorsione non strutturale")
(rifiuta "(def falso : (≡ 1 2) refl)" "atteso")
(rifiuta "(def testa-vuota : (→ (Vec A 0) A) [nil] nil)" "atteso")
(rifiuta "(extern bugia : ⊥ boh)" "riservato alla libreria standard")
(rifiuta "(def furto : Dir (%host-dir \"/etc\"))" "riservato al nucleo")
(rifiuta "(def diverse : (≡ \"a\" \"b\") refl)" "atteso")
(parameterize ([privileged #t])
  (rifiuta "(extern mente : (→ Dir ⊥) Directory.boh)" "tipo opaco")
  (rifiuta "(extern osserva : (→ Dir String) Directory.name)" "tipo opaco"))

;; --- piano ---

(define dir (format "~a/disegno-prova" (or (getenv "TMPDIR") "/tmp")))
(check-string (format "
  (def gen-config : (→ Dir Dir)
    [src] (with-file src /config/app.toml \"porta = 8080\\n\"))

  (def main : (→ [src (Host ~s)] (Export Dir))
    [src] (replace ~s (put (with-file empty /LEGGIMI \"ciao\\n\") /cfg (gen-config src))))"
  (string-append dir "/in") (string-append dir "/out")))

(define secco (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch))))))
(assert (contiene? secco "directory { withNewFile(path: \"/LEGGIMI\", contents: \"ciao\\n\") { withDirectory(path: \"/cfg\", source: \"<host { directory(path:"))
(assert (contiene? secco "withNewFile(path: \\\"/config/app.toml\\\""))
(assert (contiene? secco "} }>\") { export(path:"))
(assert (contiene? secco "wipe: true"))

;; Container: la directory dell'host entra nel container, un comando la elabora, il risultato esce.
(check-string (format "
  (def costruisci : (→ [src (Host ~s)] (Export Dir))
    [src] (replace ~s
            (pipe (container)
                  (from \"alpine\")
                  (with-dir /w src)
                  (with-workdir /w)
                  (with-exec [\"sh\" \"-c\" \"cat dati.txt dati.txt > doppio.txt\"])
                  (dir-of /w))))"
  (string-append dir "/in") (string-append dir "/out2")))
(define secco2 (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch))) 'costruisci)))
(assert (contiene? secco2 "container { from(address: \"alpine\") { withDirectory(path: \"/w\", source: \"<host"))
(assert (contiene? secco2 "withExec(args: [\"sh\", \"-c\", \"cat dati.txt dati.txt > doppio.txt\"]) { directory(path: \"/w\")"))
(rifiuta "(def mista : (List String) [\"a\" 1])" "atteso")
(rifiuta "(def pipe : Dir empty)" "parola riservata")
(check-string "(def immagini : (≡ (images (pipe (container) (from \"a\") (with-dir /w (dir-of (from container \"b\") root))))
                                  [\"a\" \"b\"])
                 auto)")
(rifiuta "(def dev-pinnate : (All pinned? (images (from container \"alpine\"))) auto)" "auto: nessuna prova di (Holds pinned? \"alpine\")")
(rifiuta "(def falso-branch : (All pinned? (images (branch (Directory.exists empty /x) (from container \"a@sha256:4bcff63911fcb4448bd4fdacec207030997caf25e9bea4045fa6c8c44de311d1\") (from container \"b\")))) auto)" "auto: nessuna prova di")
(rifiuta "(def sotto : App (app \"api\" prod 2 auto))" "auto: la proposizione si riduce a ⊥")
(rifiuta "(def falso-auto : (≡ (+ 1 1) 3) auto)" "atteso")
(check-string "(def nome-api : (≡ (App.name api) \"api\") auto)")
(check-string "(def raddoppia : (→ Nat Nat) [n] (+ n n))
               (def otto : (≡ (pipe 2 raddoppia raddoppia) 8) refl)")

;; branch: la condizione è un test nel container; i due rami sono entrambi nel piano.
(check-string (format "
  (def prova-in : (→ Dir String Container)
    [src file] (pipe (container) (from \"alpine\") (with-dir /w src) (try-exec [\"test\" \"-f\" file])))

  (def esito : (→ (Remote Bool) Dir)
    [c] (branch c (with-file empty /esito \"passa\\n\") (with-file empty /esito \"fallisce\\n\")))

  (def verifica : (→ [src (Host ~s)] (Export Dir))
    [src] (replace ~s (put (esito (passes? (prova-in src \"/w/dati.txt\")))
                           /manca (esito (exists? src /manca.txt)))))"
  (string-append dir "/in") (string-append dir "/out3")))
(define piani (all-plans 'verifica))
(assert (= (length piani) 4))
(assert (contiene? (plan->graphql (car (car (car (car piani)))))
                   "withExec(args: [\"test\", \"-f\", \"/w/dati.txt\"], expect: ANY) { exitCode }"))
(assert (equal? (map (lambda (p) (map cdr (car p))) piani) '((#t #t) (#t #f) (#f #t) (#f #f))))
(rifiuta "(def confuso : (→ (Remote Bool) Dir) [c] (if c empty empty))" "atteso")
(rifiuta "(def scelta : (→ Bool Dir) [b] (branch b empty empty))" "atteso")

;; Il contenuto dei file lo guarda Dagger: osservazioni come passes?, il testo non torna al linguaggio.
(check-string (format "
  (def contenuto : (→ [src (Host ~s)] (Export Dir))
    [src] (let [f (file-of src /dati.txt)]
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
  (def sequenza : (Export Dir)
    (then (apply (from (container) \"alpine\") [\"sh\" \"-c\" \"echo effetto\"])
          (then skip (overlay ~s (with-file empty /dopo \"sì\\n\")))))"
  (string-append dir "/out5")))
(let ([es (exits resolve-dry 'sequenza)])
  (assert (= (length es) 2))
  (assert (contiene? (plan->graphql (car es)) "withEnvVariable(name: \"DISEGNO_RUN\", value: \"<esecuzione>\") { withExec(args: [\"sh\", \"-c\", \"echo effetto\"]) { exitCode }"))
  (assert (contiene? (plan->graphql (cadr es)) "export(path:")))
;; Fuori dalla cache: due esecuzioni danno a DISEGNO_RUN valori diversi, quindi per Dagger il
;; comando è un altro; la costruzione prima della variabile resta la stessa, e resta in cache.
(let ([a (parameterize ([run-id "1"]) (plan->graphql (car (exits resolve-dry 'sequenza))))]
      [b (parameterize ([run-id "2"]) (plan->graphql (car (exits resolve-dry 'sequenza))))])
  (assert (not (string=? a b)))
  (assert (contiene? a "value: \"1\"")) (assert (contiene? b "value: \"2\"")))
(rifiuta "(def dentro : Container (with-dir (from (container) \"a\") /x (overlay \"o\" empty)))" "atteso")

;; Segreti: (Host-secret "NOME") nella firma, letto da una variabile d'ambiente. Il piano nomina la
;; variabile, mai il valore; il container lo riceve con with-secret-variable.
(check-string (format "
  (def segreto : (→ [s (Host-secret \"PATH\")] (Export Dir))
    [s] (branch (probe (with-secret-variable (from (container) \"alpine\") \"S\" s) [\"sh\" \"-c\" \"test -n \\\"$S\\\"\"])
          (overlay ~s (with-file empty /esito \"ricevuto\\n\"))
          (overlay ~s (with-file empty /esito \"vuoto\\n\"))))
  (def segreto-male : (→ [s (Host-secret \"1 X\")] (Export Dir))
    [s] skip)"
  (string-append dir "/out6") (string-append dir "/out6")))
(let ([p (plan->graphql (cadr (car (cdr (car (all-plans 'segreto))))))])
  (assert (contiene? p "withSecretVariable(name: \"S\", secret: \"<secret(uri: \\\"env://PATH\\\")>\")"))
  (assert (not (contiene? p (getenv "PATH")))))
(assert (contiene? (guard (e [#t (condition-message e)]) (all-plans 'segreto-male) "") "non è il nome di una variabile d'ambiente"))
(rifiuta "(def leggi : String (Query.secret \"env://HOME\"))" "nome sconosciuto")

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
(check-string "(def logs-bucket : Bucket \"my-app.logs\")")
(rifiuta "(def bucket-male : Bucket \"My_Bucket\")" "«My_Bucket» non è un Bucket valido")

;; AWS: la CLI fissata, con le credenziali come segreti; dal vivo risponde, senza toccare AWS.
(check-string (format "
  (def cli-aws : (→ [s (Host-secret \"PATH\")] (Export Dir))
    [s] (branch (probe (cli (aws s s \"eu-west-1\" cloud)) [\"sh\" \"-c\" \"aws --version && test -n \\\"$AWS_ACCESS_KEY_ID\\\" && test \\\"$AWS_DEFAULT_REGION\\\" = eu-west-1\"])
          (overlay ~s (with-file empty /esito \"risponde\\n\"))
          (overlay ~s (with-file empty /esito \"no\\n\"))))"
  (string-append dir "/out7") (string-append dir "/out7")))
(rifiuta "(def r : Region \"eu-west-9\")" "«eu-west-9» non è un Region valido")

;; LocalStack come service: il Parameter Store vero, emulato. Si scrive, poi si chiede; il service
;; è lo stesso per tutta la sessione. Dal vivo solo con DISEGNO_TEST_KEY (la shell lo esporta).
(check-string (format "
  (def esito-ls : (→ String (Export Dir))
    [t] (overlay ~s (with-file empty /esito t)))
  (def con-localstack : (→ [k (Host-secret \"DISEGNO_TEST_KEY\")] (Export Dir))
    [k] (let [a (aws k k \"eu-west-1\" (emulated localstack))]
          (then (put-parameter a /app/test/porta \"5432\")
          (then (put-secure-parameter a /app/test/password k)
                (branch (parameter-is? a /app/test/porta \"5432\")
                  (branch (parameter-is? a /app/test/porta \"9999\")
                    (esito-ls \"confonde i valori\\n\")
                    (branch (parameter-exists? a /app/test/password)
                      (esito-ls \"scritto\\n\")
                      (esito-ls \"manca la password\\n\")))
                  (esito-ls \"porta non scritta\\n\"))))))"
  (string-append dir "/out8")))
(assert (= (length (all-plans 'con-localstack)) 4))
;; Che cosa scrive un piano: solo le put-parameter, non gli altri effetti.
(check-string "(def scritti : (→ [a Aws] (≡ (parameters (then (put-parameter a /app/x \"1\") (apply (from (container) \"b\") [\"echo\"])))
                                           [/app/x]))
                 [a] auto)")
(assert (contiene? (plan->graphql (car (car (car (car (all-plans 'contenuto))))))
                   "withExec(args: [\"grep\", \"-qF\", \"dati\", \"/f\"], expect: ANY) { exitCode }"))

;; Extern generati dallo schema, usati direttamente: Nat e oggetti per ID negli argomenti.
(check-string "
  (def servizio : (→ [src (Host \"/x\")] (Export Dir))
    [src] (overlay \"out\" (pipe (Query.git \"https://example.com/r.git\") (GitRepository.branch \"main\") GitRef.tree
                              (put /porta (dir-of (Container.with-exposed-port (container) 8080) root)))))")
(define secco3 (plan->graphql (plan resolve-dry 'servizio)))
(assert (contiene? secco3 "git(url: \"https://example.com/r.git\") { branch(name: \"main\") { tree {"))
(assert (contiene? secco3 "withExposedPort(port: 8080)"))

;; Proprietà d'ordine: valgono per ogni input, perché effects non scende nelle directory.
(check-string "
  (def img : (→ Dir Container) [src] (pipe (container) (from \"alpine\") (with-dir /app src)))
  (def protetto : (→ Dir (Export Dir))
    [src] (branch (passes? (try-exec (from container \"alpine\") [\"true\"]))
            (branch (exists? src /VERSION) (publish (img src) \"r/app:1\") (overlay \"o\" src))
            (overlay \"o\" src)))
  (def ordine-ok : (→ [src Dir] (Before test? publish? (protetto src))) [src] auto)")
(rifiuta "(def scoperto : (→ [src Dir] (Before test? publish? (publish (img src) \"r/app:1\"))) [src] auto)"
         "si riduce a ⊥")
(rifiuta "(def finto-test : (→ [src Dir] (Before test? publish? (branch (exists? src /x) (publish (img src) \"r\") (overlay \"o\" src)))) [src] auto)"
         "si riduce a ⊥")
(rifiuta "(def nel-ramo-sbagliato : (→ [src Dir] (Before test? publish? (branch (passes? (img src)) (overlay \"o\" src) (publish (img src) \"r\")))) [src] auto)"
         "si riduce a ⊥")

;; Nomi corti: il tipo del primo argomento sceglie il metodo; senza metodo è un campo radice.
(check-string "
  (def corto : (→ [src (Host \"/x\")] (Export Dir))
    [src] (overlay \"out\" (pipe (container) (from \"alpine\") (with-mounted-cache /c (cache-volume \"k\"))
                                 (directory root) (with-new-file /a \"b\") (directory /sub))))")
(define secco4 (plan->graphql (plan resolve-dry 'corto)))
(assert (contiene? secco4 "withMountedCache(path: \"/c\", cache: \"<cacheVolume(key: \\\"k\\\")>\") { directory(path: \"/\") { withNewFile(path: \"/a\", contents: \"b\") { directory(path: \"/sub\")"))
(rifiuta "(def sbagliato : Dir (with-exec empty [\"x\"]))" "with-exec non esiste per")
(rifiuta "(def pinna : Dir (Query.cache-volume \"k\"))" "nome sconosciuto")

;; Valori raffinati e percorsi: il letterale resta, il tipo cambia; i punti non si sommano.
(rifiuta "(def c1 : Container (from container \"Golang:1.25\"))" "«Golang:1.25» non è un Image valido")
(rifiuta "(def c2 : Container (from container \"golang:1.25@sha256:abc\"))" "non è un Image valido")
(rifiuta "(def c3 : Dir (with-file empty /a/../b \"x\"))" "«..» non è un Segment valido")
(rifiuta "(def c4 : Abs (/ /out /bin))" "atteso Segment, trovato Abs")
(rifiuta "(def c5 : (⊑ /out /out/bin) auto)" "auto: nessuna prova di (⊑ /out /out/bin)")
(check-string "(def c6 : Container (from container \"ghcr.io/dagger/engine:v0.21.10\"))
               (def c7 : (⊑ (/ /out \"hello\") /out) auto)
               (def c8 : (≡ (let [o /out, b (/ o \"x\")] b) /out/x) auto)")

;; Lo spazio affine dei percorsi: la differenza esiste solo con la prova di contenimento.
(check-string "
  (def vettore : (≡ (⊖ /out/bin/hello /out auto) \"bin/hello\") auto)
  (def somma : (≡ (⊕ /out \"bin/hello\") /out/bin/hello) auto)
  (def legge-ereditata : (≡ (⊕ /out (⊖ /out/bin /out auto)) /out/bin)
    (Affine.law percorsi /out/bin /out auto))")
(rifiuta "(def storto : Rel (⊖ /out /src auto))" "auto: nessuna prova di (⊑ /out /src)")
(rifiuta "(def punti : Abs (⊕ /out /bin))" "atteso Rel, trovato Abs")

;; Regioni: montaggi sovrapposti nella stessa catena sono rifiutati; in catene diverse no.
(check-string "
  (def disgiunti : (⋔ /src /go/pkg/mod) auto)
  (def due-catene : (Disjoint-mounts (pipe (container) (with-dir /w (dir-of (pipe (container) (with-dir /w empty)) /w)))) auto)")
(rifiuta "(def annidati : (⋔ /src /src/cache) auto)" "auto: nessuna prova di (⋔ /src /src/cache)")
(rifiuta "(def sovrapposti : (→ [src Dir] (Disjoint-mounts (pipe (container) (with-dir /src src) (with-mounted-cache /src/cache (cache-volume \"c\"))))) [src] auto)"
         "auto: nessuna prova")

;; Pattern assurdi: solo dove nessun costruttore è possibile; non sono una scappatoia.
(rifiuta "(def finto-assurdo : (¬ (≡ 0 0)) [()])" "() non è assurdo: refl è possibile")
(rifiuta "(def finto-assurdo2 : (¬ (⊑ /out/x /out)) [(⊑-step ())])" "() non è assurdo")
(rifiuta "(def falso-diretto : ⊥ [()])" "troppi pattern")
(rifiuta "(def vero-negato : (¬ (⊑ /out/x /out)) auto)" "auto: nessuna refutazione di (⊑ /out/x /out)")

;; Letterali di tempo, indirizzi e porte: malformati o fuori spazio sono errori di tipo.
(rifiuta "(def t1 : Instant \"2026-13-01\")" "«2026-13-01» non è un Instant valido")
(rifiuta "(def t2 : Duration \"5x\")" "«5x» non è un Duration valido")
(rifiuta "(def t3 : Ip \"10.0.0.256\")" "«10.0.0.256» non è un Ip valido")
(rifiuta "(def t4 : Cidr \"10.0.0.1/24\")" "«10.0.0.1/24» non è un Cidr valido")
(rifiuta "(def t5 : Container (with-exposed-port (container) 70000))" "«70000» non è un Port valido")
(rifiuta "(def t6 : Instant (⊕ inizio fine))" "atteso Duration, trovato Instant")
(check-string "(def ultimo : Ip \"255.255.255.255\")")
(rifiuta "(def oltre : Ip (⊕ ultimo 1 auto))" "si riduce a ⊥")      ; l'overflow è escluso

;; Il cookbook: ogni ricetta è un programma a sé, verificato in un processo separato con
;; check (tipi e teoremi) e, se ha un main, plan (il piano a secco). Mai run: la 03 pubblica.
;; Anche i capitoli del libro (book/) e le soluzioni degli esercizi (book/solutions/) sono programmi verificati.
(for-each
  (lambda (r)
    (let* ([path (at-root r)]
           [mode (if (contiene? (call-with-input-file path get-string-all) "(def main ") "plan" "check")])
      (unless (zero? (system (format "scheme --script ~a ~a ~a >/dev/null" (at-root "src/main.ss") mode path)))
        (error 'prova (format "~a non passa (~a)" r mode)))))
  (apply append
         (map (lambda (dir)
                (map (lambda (f) (string-append dir "/" f))
                     (sort string<? (filter (lambda (f) (let ([n (string-length f)]) (and (> n 8) (string=? (substring f (- n 8) n) ".disegno"))))
                                            (directory-list (at-root dir))))))
              '("cookbook" "book" "book/solutions"))))

;; Quando auto fallisce su una congiunzione, il messaggio indica la parte che non vale.
(rifiuta "(def subnet-sovrapposte : (Disjoint-subnets [\"10.0.1.0/24\" \"10.0.2.0/24\" \"10.0.1.128/25\"]) auto)"
         "auto: nessuna prova di (Cidr-apart \"10.0.1.0/24\" \"10.0.1.128/25\")")
(rifiuta "(def porte-ripetute : (Distinct-ports (pipe (container) (with-exposed-port 80) (with-exposed-port 443) (with-exposed-port 80))) auto)"
         "auto: nessuna prova di (port≠ 80 80)")
(rifiuta "(def montaggi-annidati : (Disjoint-mounts (pipe (container) (with-dir /src empty) (with-mounted-cache /src/cache (cache-volume \"c\")))) auto)"
         "auto: nessuna prova di (⋔ /src/cache /src)")
;; Le posizioni: file:riga:colonna dell'espressione più vicina.
(rifiuta "(def ok : Nat 1)\n(def male : Abs\n  (⊕ /out /bin))" "<stringa>:3:3: /bin: atteso Rel, trovato Abs")
;; Un errore non ferma il file; chi usa un nome la cui firma è sbagliata non aggiunge errori.
(rifiuta "(def a : Nat zz)\n(def b : Bool 3)" "<stringa>:2:1: 3: atteso Bool")
;; import: solo i moduli di lib/, per nome; un percorso non passa.
(rifiuta "(import ../tests/checks)" "non è il nome di un modulo")
(rifiuta "(import nessuno)" "il modulo nessuno non esiste")
;; builtin: solo nella libreria, chiavi chiuse, una volta, del genere giusto.
(rifiuta "(builtin nat Nat)" "builtin è riservato alla libreria standard")
(parameterize ([privileged #t])
  (rifiuta "(builtin intero Nat)" "chiave sconosciuta intero")
  (rifiuta "(builtin nat Bool)" "nat è già legato a Nat"))
;; Nelle firme si generalizzano solo i nomi da variabile: Porta non è un tipo implicito.
(rifiuta "(def f : (→ Porta Nat) [_] 0)" "nome sconosciuto: Porta")
(assert (equal? (guard (e [#t (condition-message e)]) (check-string "(def f : (→ Nat \"x\") [_] 0)\n(def g : Nat (f 1))") #f)
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
              (msg "textDocument/didOpen" `(("textDocument" . (("uri" . ,uri) ("text" . "(import paths)\n(def male : Abs\n  (⊕ /out /bin))\n(def peggio : Nat \"x\")\n")))))
              (msg "textDocument/didChange" `(("textDocument" . (("uri" . ,uri))) ("contentChanges" . ,(vector '(("text" . "(import paths)\n(def bene : Abs (⊕ /out \"bin\"))\n(def r : (≡ 1 1) refl)\n"))))))
              (msg "textDocument/didSave" `(("textDocument" . (("uri" . ,uri)))))
              (msg "textDocument/hover" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 1) ("character" . 17)))) 3)
              (msg "textDocument/definition" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 2) ("character" . 18)))) 4)
              (msg "textDocument/definition" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 1) ("character" . 5)))) 5)
              (msg "textDocument/documentSymbol" `(("textDocument" . (("uri" . ,uri)))) 6)
              (msg "shutdown" '(("x" . 1)) 2)
              (msg "exit" '(("x" . 1)))))) 'replace)
  (system (format "scheme --script ~a lsp < ~a > ~a" (at-root "src/main.ss") in out))
  (let ([r (call-with-input-file out get-string-all)])
    (assert (contiene? r "\"capabilities\""))
    (assert (contiene? r "\"range\":{\"start\":{\"line\":2,\"character\":2}"))
    (assert (contiene? r "\"message\":\"/bin: atteso Rel, trovato Abs\""))
    (assert (contiene? r "\"range\":{\"start\":{\"line\":3,\"character\":0}"))   ; anche il secondo errore
    (assert (contiene? r "\"id\":4,\"result\":[{\"uri\":\"file:///"))         ; refl: nella libreria standard
    (assert (contiene? r "lib/prelude.disegno\",\"range\":{\"start\":{\"line\":6,"))
    (assert (contiene? r (format "\"id\":5,\"result\":[{\"uri\":\"~a\",\"range\":{\"start\":{\"line\":1,\"character\":0}" uri)))   ; bene: qui
    (assert (contiene? r "\"name\":\"bene\",\"kind\":12"))
    (assert (contiene? r "\"name\":\"r\",\"kind\":12"))
    (assert (contiene? r "\"diagnostics\":[]"))
    (assert (contiene? r "\"id\":3,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```disegno\\nAbs.⊕ : (→ Abs Rel Abs)\\n"))   ; e le altre varianti di ⊕
    (assert (contiene? r "\"id\":2,\"result\":null"))))

;; Nei pattern un simbolo è un costruttore solo se lo è del tipo atteso: step, port, root…
;; restano variabili dove il tipo è un altro. La copertura usa la stessa risoluzione.
(check-string "
  (def somma-step : (→ Nat (→ Nat Nat) Nat) [port step] (step port))
  (def usa-step : (≡ (somma-step 2 add1) 3) auto)")
(rifiuta "(def manca-step : (→ Rel Nat) [here] 0)" "manca il caso")

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
    (check-string (format "(def rotto : (→ (Export Dir))
    (overlay \"rotto\" (pipe (container) (from \"alpine\")
                             (with-exec [\"sh\" \"-c\" \"echo A; sleep 0.3; echo B >&2; sleep 0.3; echo C\"])
                             (with-exec [\"sh\" \"-c\" \"echo male >&2; exit 3\"]) (dir-of /tmp))))
  (def prepara : Container
    (pipe (container) (from \"alpine\") (with-exec [\"sh\" \"-c\" \"echo prep~a\"])))
  (def in-diretta : (→ [src (Host ~s)] (Export Dir))
    [src] (overlay \"rotto\" (pipe prepara (with-dir /w src)
                                   (with-exec [\"sh\" \"-c\" \"echo A~a; sleep 0.05; echo B >&2; sleep 0.05; echo C\"])
                                   (with-exec [\"sh\" \"-c\" \"echo male~a >&2; exit 3\"]) (dir-of /tmp))))"
                          n (string-append dir "/in") n n))
    (let ([r (esegui 'rotto)])
      (assert (and (car r) (contiene? (car r) "<stringa>:4:30: passo fallito (exit 3)")))
      (assert (string=? (cdr r) "")))
    (putenv "DISEGNO_LOGS" "1")
    ;; Il resoconto: una riga per voce, con i nomi del programma; prepara non vede l'input ed è
    ;; ambiente; in-diretta fallisce, e le ultime righe del passo dicono perché.
    (let* ([r (esegui 'in-diretta)] [msg (car r)] [out (cdr r)])
      (assert (> streamed 0))                                 ; le righe sono arrivate dal flusso
      (assert (contiene? out "✓ prepara     ambiente  "))
      (assert (contiene? out "✗ in-diretta  <stringa>:10:36  exit 3  "))
      (assert (contiene? out (format "\n      male~a\n" n)))
      (assert (not (contiene? out (format "A~a" n))))         ; la prova di ciò che è andato non si stampa
      (assert (and msg (contiene? msg "<stringa>:10:36: passo fallito (exit 3)"))))
    ;; In CI la prova sta nel gruppo della voce: stdout e stderr intrecciati. Il primo passo ora è
    ;; in cache: il flusso tace, e la prova è combinedOutput.
    (set! logged '())                                         ; un run nuovo, come un processo nuovo
    (putenv "GITHUB_ACTIONS" "true")
    (let ([out (cdr (esegui 'in-diretta))])
      (putenv "GITHUB_ACTIONS" "")
      (assert (contiene? out "::group::✓ prepara     ambiente  "))
      (assert (contiene? out (format "\"\nA~a\nB\nC\n" n)))
      (assert (contiene? out "::error file=<stringa>,line=10,col=36::passo fallito (exit 3)"))))
  ;; Le uscite vengono nell'ordine di then, e il resoconto mostra l'effetto con il suo comando.
  (let ([r2 (begin (set! logged '()) (esegui 'sequenza))])
    (assert (contiene? (cdr r2) "✓ sequenza    sh -c \"echo effetto\"  "))
    (assert (contiene? (cdr r2) "realizzato in "))
    (assert (contiene? (cdr r2) ": effetto sh -c \"echo effetto\", esportato "))
    (assert (string=? (call-with-input-file (string-append dir "/out5/dopo") get-string-all) "sì\n")))
  (run 'segreto)
  (assert (string=? (call-with-input-file (string-append dir "/out6/esito") get-string-all) "ricevuto\n"))
  (run 'cli-aws)
  (assert (string=? (call-with-input-file (string-append dir "/out7/esito") get-string-all) "risponde\n"))
  (when (getenv "DISEGNO_TEST_KEY")
    (run 'con-localstack)
    (assert (string=? (call-with-input-file (string-append dir "/out8/esito") get-string-all) "scritto\n")))
  (system (format "rm -rf ~a" dir))
  (display "dal vivo: ok\n"))
(display "ok\n")
