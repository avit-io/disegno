;; Il driver. Disegno ha i tre momenti di Zuccari, tre usi dello stesso programma:
;;   disegno check prog.disegno   disegno interno: tipi e teoremi
;;   disegno plan  prog.disegno   disegno esterno: il piano, un GraphQL per ogni esito dei branch
;;   disegno run   prog.disegno   opera: l'esecuzione su Dagger (il comando apre la sessione)
;;   disegno lsp                  il server LSP per gli editor (diagnostica)
;; Senza sottocomando: check se il file non ha main, altrimenti plan (o run sotto dagger run).

(define root (path-parent (path-parent (car (command-line)))))   ; <root>/src/main.ss
(define (at-root p) (if (string=? root "") p (string-append root "/" p)))

(load (at-root "src/core.ss"))
(load (at-root "src/types.ss"))
(load (at-root "src/plan.ss"))

(when (equal? (command-line-arguments) '("lsp"))         ; disegno lsp: il server per gli editor
  (load (at-root "src/lsp.ss"))
  (serve)
  (exit 0))

(define-values (mode file)
  (let ([args (command-line-arguments)])
    (cond [(and (= (length args) 2) (member (car args) '("check" "plan" "run"))) (values (string->symbol (car args)) (cadr args))]
          [(= (length args) 1) (values #f (car args))]
          [else (display "uso: disegno [check|plan|run] programma.disegno\n") (exit 2)])))

;; Gli errori del linguaggio escono nel formato dei compilatori, file:riga:colonna: messaggio,
;; su stderr e con codice 1: è quello che leggono :make e la quickfix di Neovim.
(define (report e)
  (let ([err (current-error-port)])
    (if (and (who-condition? e) (eq? (condition-who e) 'disegno) (message-condition? e))
        (display (condition-message e) err)
        (display-condition e err))
    (newline err)
    (exit 1)))

(guard (e [#t (report e)])
  (parameterize ([privileged #t]) (check-file (at-root "lib/std.disegno")))
  (check-file file))

(define has-main (hashtable-ref sigs 'main #f))
(define mode* (or mode (cond [(not has-main) 'check] [(getenv "DAGGER_SESSION_PORT") 'run] [else 'plan])))

(guard (e [#t (report e)])
  (parameterize ([program-dir (path-parent file)])
    (case mode*
      [(check) (display "disegno interno verificato: tipi e teoremi\n")]
      [(plan) (for-each (lambda (p)
                          (for-each (lambda (d) (format #t "# se ~a → ~a~%" (plan->graphql (car d)) (if (cdr d) "vero" "falso")))
                                    (car p))
                          (display (plan->graphql (cdr p)))
                          (newline))
                        (all-plans 'main))]
      [(run) (unless (getenv "DAGGER_SESSION_PORT") (oops "run richiede una sessione Dagger: usare `disegno run`"))
             (display (run 'main)) (newline)])))
