;; Uso: dagger run scheme --script disegno.ss programma.disegno
;; Senza sessione Dagger stampa il piano invece di eseguirlo.
(load "nucleo.ss")
(load "tipi.ss")
(load "piano.ss")

(parameterize ([privileged #t]) (check-file "std.disegno"))
(check-file (car (command-line-arguments)))
(display
  (if (getenv "DAGGER_SESSION_PORT")
      (submit-leaf (plan (lambda (ch) (submit-leaf (append ch '((id)))))))
      (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch)))))))
(newline)
