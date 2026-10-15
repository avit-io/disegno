;; Uso: dagger run scheme --script disegno.ss programma.disegno
;; Senza sessione Dagger stampa il piano: uno per ogni combinazione di esiti dei branch.
(load "core.ss")
(load "types.ss")
(load "plan.ss")

(parameterize ([privileged #t]) (check-file "std.disegno"))
(check-file (car (command-line-arguments)))
(if (getenv "DAGGER_SESSION_PORT")
    (begin (display (run 'main)) (newline))
    (for-each (lambda (p)
                (for-each (lambda (d) (format #t "# se ~a → ~a~%" (plan->graphql (car d)) (if (cdr d) "vero" "falso")))
                          (car p))
                (display (plan->graphql (cdr p)))
                (newline))
              (all-plans 'main)))
