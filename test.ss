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
    [src] (with-file src \"config/app.toml\" \"porta = 8080\\n\"))

  (def main : (→ [src (Host ~s)] (Export Dir))
    [src] (replace ~s (put (with-file empty \"LEGGIMI\" \"ciao\\n\") \"cfg\" (gen-config src))))"
  (string-append dir "/in") (string-append dir "/out")))

(define secco (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch))))))
(assert (contiene? secco "directory { withNewFile(path: \"LEGGIMI\", contents: \"ciao\\n\") { withDirectory(path: \"cfg\", source: \"<host { directory(path:"))
(assert (contiene? secco "withNewFile(path: \\\"config/app.toml\\\""))
(assert (contiene? secco "} }>\") { export(path:"))
(assert (contiene? secco "wipe: true"))

;; Container: la directory dell'host entra nel container, un comando la elabora, il risultato esce.
(check-string (format "
  (def costruisci : (→ [src (Host ~s)] (Export Dir))
    [src] (replace ~s
            (pipe (container)
                  (from \"alpine\")
                  (with-dir \"/w\" src)
                  (with-workdir \"/w\")
                  (with-exec [\"sh\" \"-c\" \"cat dati.txt dati.txt > doppio.txt\"])
                  (dir-of \"/w\"))))"
  (string-append dir "/in") (string-append dir "/out2")))
(define secco2 (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch))) 'costruisci)))
(assert (contiene? secco2 "container { from(address: \"alpine\") { withDirectory(path: \"/w\", source: \"<host"))
(assert (contiene? secco2 "withExec(args: [\"sh\", \"-c\", \"cat dati.txt dati.txt > doppio.txt\"]) { directory(path: \"/w\")"))
(rifiuta "(def mista : (List String) [\"a\" 1])" "atteso")
(rifiuta "(def pipe : Dir empty)" "parola riservata")
(check-string "(def immagini : (≡ (images (pipe (container) (from \"a\") (with-dir \"/w\" (dir-of (from container \"b\") \"/\"))))
                                  [\"a\" \"b\"])
                 auto)")
(rifiuta "(def dev-pinnate : (All pinned? (images (from container \"alpine\"))) auto)" "si riduce a ⊥")
(rifiuta "(def falso-branch : (All pinned? (images (branch (Directory.exists empty \"x\") (from container \"a@sha256:1\") (from container \"b\")))) auto)" "si riduce a ⊥")
(rifiuta "(def sotto : Service (service \"api\" prod 2 auto))" "auto: la proposizione si riduce a ⊥")
(rifiuta "(def falso-auto : (≡ (+ 1 1) 3) auto)" "atteso")
(check-string "(def nome-api : (≡ (Service.name api) \"api\") auto)")
(check-string "(def raddoppia : (→ Nat Nat) [n] (+ n n))
               (def otto : (≡ (pipe 2 raddoppia raddoppia) 8) refl)")

;; branch: la condizione è un test nel container; i due rami sono entrambi nel piano.
(check-string (format "
  (def prova-in : (→ Dir String Container)
    [src file] (pipe (container) (from \"alpine\") (with-dir \"/w\" src) (try-exec [\"test\" \"-f\" file])))

  (def esito : (→ (Remote Bool) Dir)
    [c] (branch c (with-file empty \"esito\" \"passa\\n\") (with-file empty \"esito\" \"fallisce\\n\")))

  (def verifica : (→ [src (Host ~s)] (Export Dir))
    [src] (replace ~s (put (esito (passes? (prova-in src \"/w/dati.txt\")))
                           \"manca\" (esito (exists? src \"manca.txt\")))))"
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
                              (put \"porta\" (dir-of (Container.with-exposed-port (container) 8080) \"/\")))))")
(define secco3 (plan->graphql (plan resolve-dry 'servizio)))
(assert (contiene? secco3 "git(url: \"https://example.com/r.git\") { branch(name: \"main\") { tree {"))
(assert (contiene? secco3 "withExposedPort(port: 8080)"))

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
