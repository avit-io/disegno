;; Controlli: nucleo, type checker, piano (a secco) e, sotto `dagger run`, esecuzione dal vivo.
(load "core.ss")
(load "types.ss")
(load "plan.ss")

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

(parameterize ([privileged #t]) (check-file "std.disegno"))
(check-file "examples.disegno")

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
(rifiuta "(def dev-pinnate : (All pinned? (images (from container \"alpine\"))) auto)" "si riduce a ⊥")
(rifiuta "(def falso-branch : (All pinned? (images (branch (Directory.exists empty /x) (from container \"a@sha256:4bcff63911fcb4448bd4fdacec207030997caf25e9bea4045fa6c8c44de311d1\") (from container \"b\")))) auto)" "si riduce a ⊥")
(rifiuta "(def sotto : Service (service \"api\" prod 2 auto))" "auto: la proposizione si riduce a ⊥")
(rifiuta "(def falso-auto : (≡ (+ 1 1) 3) auto)" "atteso")
(check-string "(def nome-api : (≡ (Service.name api) \"api\") auto)")
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

;; --- dal vivo ---








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
  (system (format "rm -rf ~a" dir))
  (display "dal vivo: ok\n"))
(display "ok\n")
