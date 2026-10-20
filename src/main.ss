;; Il driver. Disegno ha i tre momenti di Zuccari, tre usi dello stesso programma:
;;   disegno check prog.disegno   disegno interno: tipi e teoremi
;;   disegno plan  prog.disegno   disegno esterno: il piano, un GraphQL per ogni esito dei branch
;;   disegno run   prog.disegno   opera: l'esecuzione su Dagger (il comando apre la sessione)
;;   disegno lsp                  il server LSP per gli editor (diagnostica)
;; Senza sottocomando: check se il file non ha main, altrimenti plan (o run sotto dagger api with-session).

(define root (path-parent (path-parent (car (command-line)))))   ; <root>/src/main.ss
(define (at-root p) (if (string=? root "") p (string-append root "/" p)))

(load (at-root "src/core.ss"))
(load (at-root "src/types.ss"))
(load (at-root "src/plan.ss"))

(when (equal? (command-line-arguments) '("lsp"))         ; disegno lsp: il server per gli editor
  (load (at-root "src/lsp.ss"))
  (serve)
  (exit 0))

;; disegno type prog.disegno nome: il tipo di un nome globale (usato dall'hover dell'LSP);
;; disegno where prog.disegno nome: dove è definito, file:riga:colonna (la definizione).
;; Il file si controlla fin dove si può: un errore non impedisce di conoscere i nomi definiti.
;; Un nome corto risolto dal tipo (from, with-exec…) mostra tutte le sue varianti.
(let ([args (command-line-arguments)])
  (when (and (= (length args) 3) (member (car args) '("type" "where")))
    (import! 'prelude)
    (guard (e [#t #f]) (check-file (cadr args)))
    (let* ([name (string->symbol (caddr args))]
           [names (if (gget name) (list name) (qualified name))]
           [lines (if (equal? (car args) "where")
                      (filter values (map (lambda (n) (let ([p (hashtable-ref def-pos n #f)]) (and p (pos->string p)))) names))
                      (if (and (not (gget name)) (path-literal? name))
                          (list (format "~a : ~a" name (bi 'abs)))
                          (filter values (map type-of-global names))))])
      (if (null? lines)
          (exit 1)
          (begin (for-each (lambda (l) (display l) (newline)) lines) (exit 0))))))

(define-values (mode file)
  (let ([args (command-line-arguments)])
    (cond [(and (= (length args) 2) (member (car args) '("check" "plan" "run"))) (values (string->symbol (car args)) (cadr args))]
          [(= (length args) 1) (values #f (car args))]
          [else (display "uso: disegno [check|plan|run] programma.disegno\n") (exit 2)])))

;; Gli errori del linguaggio escono nel formato dei compilatori, file:riga:colonna: messaggio,
;; su stderr e con codice 1: è quello che leggono :make e la quickfix di Neovim.
(define (report e)
  (let ([err (current-error-port)])
    (cond [(and (who-condition? e) (eq? (condition-who e) 'disegno) (message-condition? e))
           (display (condition-message e) err)]
          [(and (who-condition? e) (eq? (condition-who e) 'motore) (message-condition? e))   ; senza le extensions
           (display (string-append "motore: " (condition-message e)) err)]
          [else (display-condition e err)])
    (newline err)
    (exit 1)))

(guard (e [#t (report e)])
  (import! 'prelude)
  (check-file file))

(define has-main (hashtable-ref sigs 'main #f))
(define mode* (or mode (cond [(not has-main) 'check] [(getenv "DAGGER_SESSION_PORT") 'run] [else 'plan])))

(guard (e [#t (report e)])
  (parameterize ([program-dir (path-parent file)])
    (case mode*
      [(check) (display "disegno interno verificato: tipi e teoremi\n")]
      [(plan) (let ([ps (all-plans 'main)])     ; per ogni esito: osservazioni e uscite, in ordine
               (for-each (lambda (p i)
                          (when (> i 0) (newline))
                          (for-each (lambda (ev)
                                      (case (car ev)
                                        [(se) (format #t "# se ~a → ~a~%" (plan->graphql (cadr ev)) (if (caddr ev) "vero" "falso"))]
                                        [(altrimenti) (display "# se qualcosa prima fallisce:\n")]
                                        [(fallisce) (format #t "# fallisce: ~a~%" (cadr ev))]
                                        [else (display (plan->graphql (cadr ev))) (newline)]))
                                    (cdr p)))
                        ps (iota (length ps))))]
      [(run) (unless (getenv "DAGGER_SESSION_PORT") (oops "run richiede una sessione Dagger: usare `disegno run`"))
             (let ([r (run 'main)]) (unless (env? "DISEGNO_LOGS") (display r) (newline)))])))   ; con il resoconto, la riga finale dice già dove
