;; Generates engine.disegno from the engine's schema (introspection on the session).
;; Usage: dagger api with-session scheme --script tools/gen.ss
;;
;; The plan is data: every engine field becomes a constructor of the family
;; (data Obj : (→ Kind Type) ...), indexed by the GraphQL type (Kind.container, ...).
;; The constructor's name gives the field (Container.with-exec → withExec), the binders the arguments.
;; Only the types in `allowed`, only required arguments and the promoted ones (`promoted`); fields
;; that cannot be expressed are skipped.
;; A Boolean result becomes an observation, (Obj Kind.bool).
(define root (path-parent (path-parent (car (command-line)))))   ; <root>/tools/gen.ss
(define (at-root p) (if (string=? root "") p (string-append root "/" p)))
(load (at-root "src/core.ss"))

(define allowed '("Container" "Directory" "File" "CacheVolume" "GitRepository" "GitRef" "Secret" "Service"))

(define typeref "type { kind name ofType { kind name ofType { kind name ofType { kind name } } } }")
(define schema
  (let ([r (json-read (query (format "{ __schema { types { name kind fields { name isDeprecated args { name defaultValue directives { name args { name value } } ~a } ~a } } } }"
                                     typeref typeref)))])
    (cdr (assoc "types" (cdr (assoc "__schema" (cdr (assoc "data" r))))))))

(define (get o k) (cdr (assoc k o)))

(define (kebab s)                                        ; withNewFile → with-new-file
  (list->string
    (let loop ([cs (string->list s)] [prev #f])
      (cond [(null? cs) '()]
            [(and (char-upper-case? (car cs)) prev (not (char-upper-case? prev)))
             (cons* #\- (char-downcase (car cs)) (loop (cdr cs) (car cs)))]
            [else (cons (char-downcase (car cs)) (loop (cdr cs) (car cs)))]))))

(define (camel s)                                        ; with-new-file → withNewFile (as in plan.ss)
  (let loop ([cs (string->list s)] [up #f])
    (cond [(null? cs) ""]
          [(char=? (car cs) #\-) (loop (cdr cs) #t)]
          [else (string-append (string (if up (char-upcase (car cs)) (car cs))) (loop (cdr cs) #f))])))

(define (obj k) (list 'Obj (string->symbol (string-append "Kind." (kebab k)))))

(define (expected a)                                     ; IDs are generic: the type is in @expectedType
  (let ([d (find (lambda (d) (equal? (get d "name") "expectedType")) (get a "directives"))])
    (and d (json-read (get (car (get d "args")) "value")))))

;; Refined types by argument name: the schema says String, the design knows more.
;; ponytail: a rule by name, enough for Dagger; if a name changes meaning a per-field table will be needed.
(define refined '(("path" String Abs) ("address" String Image) ("args" (List String) (List Arg)) ("port" Nat Port)))

(define (arg-type a)
  (let ([t (base-type a)] [r (assoc (get a "name") refined)])
    (if (and r (equal? t (cadr r))) (caddr r) t)))

(define (base-type a)
  (let loop ([t (get a "type")])
    (let ([k (get t "kind")] [n (get t "name")])
      (cond [(equal? k "NON_NULL") (loop (get t "ofType"))]
            [(equal? k "LIST") (let ([e (loop (get t "ofType"))])   ; lists of texts or of objects (by ID)
                                  (cond [(memq e '(String Build-arg)) `(List ,e)] [(and (pair? e) (eq? (car e) 'Obj)) `(List ,e)] [else #f]))]
            [(equal? n "String") 'String]
            [(equal? n "Int") 'Nat]                     ; ponytail: Int → Nat, ports and counts are enough
            [(equal? n "Boolean") 'Bool]
            [(and (equal? k "INPUT_OBJECT") (equal? n "BuildArg")) 'Build-arg]   ; (build-arg name value)
            [(equal? n "ID") (let ([e (expected a)]) (and e (member e allowed) (obj e)))]
            [else #f]))))

(define (result-type t)
  (let ([k (get t "kind")] [n (get t "name")])
    (cond [(equal? k "NON_NULL") (result-type (get t "ofType"))]
          [(and (equal? k "OBJECT") (member n allowed)) (obj n)]
          [(and (equal? k "SCALAR") (equal? n "Boolean")) (obj "bool")]
          [else #f])))

(define (required? a) (and (equal? (get (get a "type") "kind") "NON_NULL") (eq? (get a "defaultValue") 'null)))

;; Promoted optional arguments: for these fields the constructor asks for them, in the schema's
;; order. Whoever does not need them uses a curated library name, which passes the default.
;; ponytail: a hand-written list, field by field; it grows when a library needs it.
(define promoted
  '(("Directory" "filter" "include" "exclude")           ; the globs of files to keep and to drop
    ("Directory" "withNewFile" "permissions")            ; an executable file
    ("Container" "asService" "useEntrypoint")           ; a service with the image's entrypoint
    ("Directory" "dockerBuild" "dockerfile" "buildArgs" "secrets"))) ; a Dockerfile build, with arguments and secrets (id = the secret's name)

(define (wanted? type n a)
  (or (required? a)
      (let ([p (find (lambda (p) (and (equal? (car p) type) (equal? (cadr p) n))) promoted)])
        (and p (member (get a "name") (cddr p)) #t))))

;; Constructor: (name ((argument type) ...) result), or #f if the field cannot be expressed.
(define (constructor type f)
  (let* ([n (get f "name")]
         [args (filter (lambda (a) (wanted? type n a)) (get f "args"))]
         [ats (map arg-type args)]
         [res (result-type (get f "type"))])
    (and res (not (get f "isDeprecated")) (for-all values ats) (not (and (equal? type "Query") (member n excluded)))
         (string=? (camel (kebab n)) n)                  ; the runner must be able to get back to the field
         (list (string->symbol (format "~a.~a" type (kebab n)))
               (append (if (equal? type "Query") '() (list (list 'self (obj type))))
                       (map (lambda (a t) (list (string->symbol (get a "name")) t)) args ats))
               res))))

(define (constructors type)
  (filter values (map (lambda (f) (constructor type f))
                      (list-sort (lambda (a b) (string<? (get a "name") (get b "name")))   ; the 1.0 schema is not sorted
                                 (get (find (lambda (t) (equal? (get t "name") type)) schema) "fields")))))

;; The core's junctions: constructors too, but the runner realizes them (plan.ss).
(define core-nodes
  `((%host-dir ((path String)) ,(obj "directory"))
    (%host-secret ((name String)) ,(obj "secret"))       ; the secret of a host environment variable
    (try-exec ((self ,(obj "container")) (args (List Arg))) ,(obj "container"))
    (passes? ((self ,(obj "container"))) ,(obj "bool"))
    (branch ((cond ,(obj "bool")) (then (Obj k)) (else (Obj k))) (Obj k))
    (overlay ((path String) (dir ,(obj "directory"))) ,(obj "export"))
    (replace ((path String) (dir ,(obj "directory"))) ,(obj "export"))
    (publish ((self ,(obj "container")) (address Image)) ,(obj "export"))
    ;; Effects in sequence: apply runs a command as an effect (outside the cache), then realizes
    ;; two outputs in order, skip is the empty output, probe observes the world outside the cache.
    (apply ((self ,(obj "container")) (args (List Arg))) ,(obj "export"))
    (then ((first ,(obj "export")) (second ,(obj "export"))) ,(obj "export"))
    (skip () ,(obj "export"))
    ;; If a fails b is realized (a report, a rollback), then it fails anyway.
    (otherwise ((first ,(obj "export")) (second ,(obj "export"))) ,(obj "export"))
    ;; An output that fails with a message: a check on the parameters, a refusal.
    (fail ((message String)) ,(obj "export"))
    ;; A background service: started here, it stays alive until the end of the session, and the
    ;; steps binding it use this instance. Without start, Dagger stops it when nobody uses it.
    (start ((self ,(obj "service"))) ,(obj "export"))
    (probe ((self ,(obj "container")) (args (List Arg))) ,(obj "bool"))
    ;; Like with-exec, but outside the cache: to read the world, like a git clone of a branch.
    (with-fresh-exec ((self ,(obj "container")) (args (List Arg))) ,(obj "container"))
    ;; A secret read at run time: cmd, in self, prints it; the runner hands it to Dagger
    ;; (setSecret) when a step uses it. The value never comes back to the language.
    (secret-from ((self ,(obj "container")) (args (List Arg)) (name String)) ,(obj "secret"))   ; name: the secret's id (a Dockerfile looks it up so)
    ;; The only state that persists from one run to the next, not content-addressed: that is
    ;; why it is a declared junction and not a generated field.
    (cache-volume ((key String)) ,(obj "cache-volume"))))

(define excluded '("cacheVolume"                     ; root fields made into core junctions
                   "secret" "setSecret"))            ; a secret comes in only from main's signature (Host-secret)

(define all (append core-nodes (apply append (map constructors (cons "Query" allowed)))))

(define (signature c)
  (if (null? (cadr c)) (caddr c)
      (format "(Π (~{~a~^ ~}) ~a)" (map (lambda (b) (format "(~a ~a)" (car b) (cadr b))) (cadr c)) (caddr c))))

(define (obj? t) (and (pair? t) (eq? (car t) 'Obj)))

;; nodes: all the sub-plans, by structural recursion on every constructor.
(define (nodes-clause c)
  (let* ([xs (map (lambda (i) (string->symbol (format "x~a" i))) (iota (length (cadr c))))]
         [self (if (null? xs) (car c) (cons (car c) xs))]
         [subs (filter values (map (lambda (b x) (and (obj? (cadr b)) x)) (cadr c) xs))])
    (format "    (~a (:: (any ~a) ~a))"
            self self (fold-right (lambda (x acc) (format "(++ (nodes ~a) ~a)" x acc)) "nil" subs))))

;; chain: the nodes along self's chain (a container and its steps), without going down into the
;; arguments; branch goes on in both branches.
(define (chain-clause c)
  (let* ([xs (map (lambda (i) (string->symbol (format "x~a" i))) (iota (length (cadr c))))]
         [self (if (null? xs) (car c) (cons (car c) xs))]
         [rest (cond [(eq? (car c) 'branch) "(++ (chain x1) (chain x2))"]
                     [(and (pair? (cadr c)) (eq? (car (car (cadr c))) 'self)) "(chain x0)"]
                     [else "nil"])])
    (format "    (~a (:: (any ~a) ~a))" self self rest)))

(call-with-output-file (at-root "lib/engine.disegno")
  (lambda (p)
    (format p "; Generated by gen.ss from Dagger's schema: do not edit by hand.~%~%")
    (format p "(data Kind~%~{  (~a)~^~%~})~%~%"
            (map (lambda (k) (cadr (obj k))) (append allowed '("bool" "export"))))
    (format p "; An argument of a Dockerfile build: name and value (the schema's BuildArg).~%(data Build-arg~%  (build-arg String String))~%~%")
    (format p "(data Obj : (→ Kind Type)~%~{  (~a : ~a)~^~%~})~%(builtin obj Obj)~%~%"
            (apply append (map (lambda (c) (list (car c) (signature c))) all)))
    (for-each (lambda (k) (format p "(claim ~a Type)~%(define ~a ~a)~%~%" k k (obj k))) allowed)
    (format p "; Any sub-plan, of any type.~%(data Any~%  (any (Obj k)))~%~%")
    (format p "(claim nodes (→ (Obj k) (List Any)))~%(define (nodes n)~%  (match n~%~{~a~^~%~}))~%~%" (map nodes-clause all))
    (format p "(claim chain (→ (Obj k) (List Any)))~%(define (chain n)~%  (match n~%~{~a~^~%~}))~%" (map chain-clause all)))
  'replace)
(format #t "engine.disegno written: ~a constructors~%" (length all))
