;; Disegno ha i tre momenti di Zuccari, che sono tre usi dello stesso programma:
;;   disegno interno  scheme --script disegno.ss prog.disegno   senza main: tipi e teoremi
;;   disegno esterno  scheme --script disegno.ss prog.disegno   con main: il piano, uno per ogni esito dei branch
;;   opera            dagger run scheme --script disegno.ss prog.disegno   l'esecuzione su Dagger
(load "core.ss")
(load "types.ss")
(load "plan.ss")

(parameterize ([privileged #t]) (check-file "std.disegno"))
(check-file (car (command-line-arguments)))
(cond [(not (hashtable-ref sigs 'main #f)) (display "disegno interno verificato: tipi e teoremi\n")]
      [(getenv "DAGGER_SESSION_PORT") (display (run 'main)) (newline)]
      [else (for-each (lambda (p)
                        (for-each (lambda (d) (format #t "# se ~a → ~a~%" (plan->graphql (car d)) (if (cdr d) "vero" "falso")))
                                  (car p))
                        (display (plan->graphql (cdr p)))
                        (newline))
                      (all-plans 'main))])
