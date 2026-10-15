;; Uso: dagger run scheme --script disegno.ss programma.disegno
;; Senza sessione Dagger stampa il piano: uno per ogni combinazione di esiti dei branch.
;; Un file senza main (per esempio checks.disegno) si controlla e basta: tipi e teoremi.
(load "core.ss")
(load "types.ss")
(load "plan.ss")

(parameterize ([privileged #t]) (check-file "std.disegno"))
(check-file (car (command-line-arguments)))
(cond [(not (hashtable-ref sigs 'main #f)) (display "tipi e teoremi verificati\n")]
      [(getenv "DAGGER_SESSION_PORT") (display (run 'main)) (newline)]
      [else (for-each (lambda (p)
                        (for-each (lambda (d) (format #t "# se ~a → ~a~%" (plan->graphql (car d)) (if (cdr d) "vero" "falso")))
                                  (car p))
                        (display (plan->graphql (cdr p)))
                        (newline))
                      (all-plans 'main))])
