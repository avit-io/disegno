;; The driver. Disegno has Zuccari's three moments, three uses of the same program:
;;   disegno check prog.disegno   inner design: types and theorems
;;   disegno plan  prog.disegno   outer design: the plan, one GraphQL per outcome of the branches
;;   disegno run   prog.disegno   the work: execution on Dagger (the command opens the session)
;;   disegno lsp                  the LSP server for editors
;; With no subcommand: check if the file has no main, otherwise plan (or run under dagger api with-session).

(define root (path-parent (path-parent (car (command-line)))))   ; <root>/src/main.ss
(define (at-root p) (if (string=? root "") p (string-append root "/" p)))

(load (at-root "src/core.ss"))
(load (at-root "src/types.ss"))
(load (at-root "src/plan.ss"))

(when (equal? (command-line-arguments) '("lsp"))         ; disegno lsp: the server for editors
  (load (at-root "src/lsp.ss"))
  (serve)
  (exit 0))

;; Commands for the LSP. The file is checked as far as it goes: an error does not hide the names
;; defined. With a position (line and column from 0) a local there wins over a global.
;;   disegno type prog.disegno name [line col]    the type; a short name (from, with-exec…) shows all its variants
;;   disegno where prog.disegno name [line col]   where it is defined, file:line:col
;;   disegno names prog.disegno [line col]        the names in scope, locals first, one per line
(let* ([args (command-line-arguments)] [n (length args)])
  (define (load-program file)
    (import! 'prelude)
    (parameterize ([scope-log (box '())])
      (guard (e [#t #f]) (check-file file))
      (scope-log)))
  (define (offset file rest)                             ; → offset of (line col), or #f
    (and (= (length rest) 2) (string->number (car rest)) (string->number (cadr rest))
         (offset-at file (string->number (car rest)) (string->number (cadr rest)))))
  (define (answer lines) (if (null? lines) (exit 1) (begin (for-each (lambda (l) (display l) (newline)) lines) (exit 0))))
  (when (and (memv n '(3 5)) (member (car args) '("type" "where")))
    (let* ([file (cadr args)] [log (load-program file)] [off (offset file (cdddr args))]
           [local (and off (parameterize ([scope-log log]) (local-at file off (caddr args))))]
           [name (string->symbol (caddr args))]
           [names (if (gget name) (list name) (qualified name))])
      (answer
        (cond [(and local (equal? (car args) "type")) (list (format "~a : ~a" name (car local)))]
              [(and local (cdr local)) (list (pos->string (cons file (cdr local))))]
              [(equal? (car args) "where")
               (filter values (map (lambda (n) (let ([p (hashtable-ref def-pos n #f)]) (and p (pos->string p)))) names))]
              [(and (not (gget name)) (path-literal? name)) (list (format "~a : ~a" name (bi 'abs)))]
              [else (filter values (map type-of-global names))]))))
  ;; A Type.name also gives its short form, resolved by the type of the first argument.
  (when (and (memv n '(2 4)) (equal? (car args) "names"))
    (let* ([file (cadr args)] [log (load-program file)] [off (offset file (cddr args))]
           [locals (if off (map car (parameterize ([scope-log log]) (locals-at file off))) '())]
           [seen (make-hashtable string-hash string=?)])
      (for-each (lambda (s) (hashtable-set! seen s #t)) locals)
      (vector-for-each
        (lambda (n)
          (let* ([s (symbol->string n)] [dot (let loop ([i (- (string-length s) 1)]) (cond [(< i 1) #f] [(char=? (string-ref s i) #\.) i] [else (loop (- i 1))]))])
            (unless (char=? (string-ref s 0) #\%)
              (hashtable-set! seen s #t)
              (when dot (hashtable-set! seen (substring s (+ dot 1) (string-length s)) #t)))))
        (hashtable-keys globals))
      (answer (append locals (filter (lambda (s) (not (member s locals))) (list-sort string<? (vector->list (hashtable-keys seen)))))))))

(define-values (mode file)
  (let ([args (command-line-arguments)])
    (cond [(and (= (length args) 2) (member (car args) '("check" "plan" "run"))) (values (string->symbol (car args)) (cadr args))]
          [(= (length args) 1) (values #f (car args))]
          [else (display "usage: disegno [check|plan|run] program.disegno\n") (exit 2)])))

;; Language errors come out in the compilers' format, file:line:col: message, on stderr
;; with exit code 1: that is what :make and Neovim's quickfix read.
(define (report e)
  (let ([err (current-error-port)])
    (cond [(and (who-condition? e) (eq? (condition-who e) 'disegno) (message-condition? e))
           (display (condition-message e) err)]
          [(and (who-condition? e) (eq? (condition-who e) 'engine) (message-condition? e))   ; without the extensions
           (display (string-append "engine: " (condition-message e)) err)]
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
      [(check) (display "checked: types and theorems\n")]
      [(plan) (let ([ps (all-plans 'main)])     ; for each outcome: observations and outputs, in order
               (for-each (lambda (p i)
                          (when (> i 0) (newline))
                          (for-each (lambda (ev)
                                      (case (car ev)
                                        [(if) (format #t "# if ~a → ~a~%" (plan->graphql (cadr ev)) (if (caddr ev) "true" "false"))]
                                        [(otherwise) (display "# if something before fails:\n")]
                                        [(fails) (format #t "# fails: ~a~%" (cadr ev))]
                                        [else (display (plan->graphql (cadr ev))) (newline)]))
                                    (cdr p)))
                        ps (iota (length ps))))]
      [(run) (unless (getenv "DAGGER_SESSION_PORT") (oops "run needs a Dagger session: use `disegno run`"))
             (let ([r (run 'main)]) (unless (env? "DISEGNO_LOGS") (display r) (newline)))])))   ; with the report, the last line already says where
