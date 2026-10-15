;; Controllo del nucleo: stampa (sempre) e invio (solo sotto `dagger run`).
(load "nucleo.ss")

(define ciao '((container) (from (address "alpine")) (withExec (args ("echo" "ciao"))) (stdout)))
(assert (string=? (plan->graphql ciao)
                  "container { from(address: \"alpine\") { withExec(args: [\"echo\", \"ciao\"]) { stdout } } }"))
(assert (string=? (base64 (string->utf8 "tok:")) "dG9rOg=="))
(assert (string=? (json-string "a\"b\n") "\"a\\\"b\\n\""))

;; Livello 1, file system puro del motore: nessun registry, nessuna rete.
(define fs '((directory) (withNewFile (path "a.txt") (contents "ciao\n")) (file (path "a.txt")) (contents)))

(when (getenv "DAGGER_SESSION_PORT")
  (let ([r (submit fs)])
    (display r) (newline)
    (assert (string=? r "{\"data\":{\"directory\":{\"withNewFile\":{\"file\":{\"contents\":\"ciao\\n\"}}}}}"))))
(display "ok\n")
