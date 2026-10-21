;; Checks: core, type checker, plan (dry) and, under `dagger api with-session`, live execution.
;; Usage: scheme --script tests/test.ss   (live: dagger api with-session scheme --script tests/test.ss)
(define root (path-parent (path-parent (car (command-line)))))   ; <root>/tests/test.ss
(define (at-root p) (if (string=? root "") p (string-append root "/" p)))
(load (at-root "src/core.ss"))
(load (at-root "src/types.ss"))
(load (at-root "src/plan.ss"))

(define (contains? s sub)
  (let ([n (string-length s)] [k (string-length sub)])
    (let loop ([i 0]) (and (<= (+ i k) n) (or (string=? (substring s i (+ i k)) sub) (loop (+ i 1)))))))

;; --- core ---

(define hello '((container) (from (address "alpine")) (withExec (args ("echo" "hello"))) (stdout)))
(assert (string=? (plan->graphql hello)
                  "container { from(address: \"alpine\") { withExec(args: [\"echo\", \"hello\"]) { stdout } } }"))
(assert (string=? (base64 (string->utf8 "tok:")) "dG9rOg=="))
(assert (string=? (json-string "a\"b\n") "\"a\\\"b\\n\""))
(assert (equal? (json-read "{\"data\": {\"a\": [1, true, null, \"x\\u0041\\n\"]}}")
                '(("data" ("a" 1 #t null "xA\n")))))

;; --- type checker ---

(import! 'prelude)
(for-each import! '(dagger time net files aws git argocd)) ; for the snippets below; the recipes import by themselves
;; Acceleration is trusted: on small numbers it must agree with the unary clauses.
(for-each
  (lambda (f)
    (for-each
      (lambda (a)
        (for-each
          (lambda (b)
            (let* ([t (fold-left (lambda (acc x) `(app ,acc (num ,x) e)) `(glob ,(bi (car f))) (list-head (list a b) (cadr f)))]
                   [on (reify 0 (ev '() t))]
                   [off (parameterize ([accelerate #f]) (reify 0 (ev '() t)))])
              (unless (equal? on off) (error 'test (format "acceleration of ~a on ~a ~a: ~s instead of ~s" (car f) a b on off)))))
          (iota 7)))
      (iota 7)))
  fast)

(check-file (at-root "cookbook/00-basics.disegno"))
(check-file (at-root "tests/checks.disegno"))                          ; the laws and the guarantees, as theorems

(define (rejects src expected)
  (let ([msg (guard (e [(message-condition? e) (condition-message e)]) (check-string src) #f)])
    (unless (and msg (contains? msg expected))
      (error 'test (format "~a: expected an error with «~a», got ~s" src expected msg)))))

(rejects "(claim absurd ⊥)
(define absurd absurd)" "recursion is not structural")
(rejects "(claim postulate ⊥)" "claim without define")
(rejects "(data Bad (mk (→ Bad ⊥)))" "strictly positively")
;; Nested in a list is day-end (List is strictly positive in its parameter); under an arrow it is not.
(check-string "(data Rose (node (List Rose)))")
;; The docstring is an item's label, and the items without one that it calls inherit it.
(check-string "(claim with-doc Container)
(define with-doc \"prepares the container\" (pipe (container) (from \"alpine\")))
(claim without-doc Container)
(define without-doc (pipe (container) (from \"alpine\")))")
(assert (equal? (item-doc 'with-doc) "prepares the container"))
(assert (not (item-doc 'without-doc)))
(assert (eq? (parameterize ([current-item 'with-doc]) (enter-item 'without-doc)) 'with-doc))
(assert (eq? (parameterize ([current-item 'without-doc]) (enter-item 'with-doc)) 'with-doc))
(rejects "(claim two Nat)
(define two 1 2)" "define:")
;; In the report a secret read before the item opens goes below it, and two stretches of the
;; same item make one line.
(let ([out (with-output-to-string
             (lambda ()
               (secret-line "secret a read")
               (report-item #t 'with-doc "cmd" #f 1000000000 "" "" '())
               (report-item #t 'with-doc "cmd" #f 1000000000 "" "" '())
               (release!)))])
  (assert (contains? out "prepares the container"))
  (assert (contains? out "2.0s"))
  (assert (contains? out "\n    ↳ secret a read\n")))
;; A question, an item returning (Remote Bool), gives the observation its docstring; its steps
;; belong to the item that asks it.
(check-string "(claim has-file? (→ String (Remote Bool)))
(define (has-file? p) \"is the file there?\" (probe (pipe (container) (from \"alpine\")) (list \"test\" \"-f\" p)))
(claim asks (Export Dir))
(define asks \"checks\" (unless (has-file? \"/x\") (apply (pipe (container) (from \"alpine\")) (list \"true\"))))")
(let ([seen #f])
  (parameterize ([observe (lambda (ch) (set! seen ch) #f)]) (exits resolve-dry 'asks))
  (let ([exec (list-ref seen (- (length seen) 2))])
    (assert (eq? (hashtable-ref step-question exec #f) 'has-file?))
    (assert (eq? (item-of exec) 'asks))))
;; TODO, as in Pie: every hole of the define with its context and goal, solved after
;; unification; the define is rejected.
(let ([m (guard (e [(message-condition? e) (condition-message e)])
           (check-string "(claim plus-zero (Π ((n Nat)) (≡ (+ n 0) n)))
(define (plus-zero n)
  (match n
    (zero TODO)
    ((add1 k) (cong add1 TODO))))") #f)])
  (assert (and m (contains? m "TODO\n  ──────────\n  (≡ 0 0)")))
  (assert (contains? m "<string>:5:26: TODO\n  k : Nat\n  ──────────\n  (≡ (+ k 0) k)")))
(rejects "(claim t Type)
(define t (the TODO Nat))" "is not known here")
(rejects "(data Bad2 (mk2 (List (→ Bad2 ⊥))))" "strictly positively")
(rejects "(claim type-in-type Type)
(define type-in-type Type)" "expected")
(rejects "(data U : Type (u : (→ Type U)))" "level")
(rejects "(claim pred (→ Nat Nat))
(define (pred n)
  (match n
    ((add1 k) k)))" "missing case")
(rejects "(claim pick (→ (Either A B) (→ A C) (→ B C) C))
(define (pick n f _)
  (match n
    ((left a) (f a))))" "missing case (pick (right _) _ _)")   ; as a call, without metavariables
(rejects "(claim spin (→ Nat Nat))
(define (spin n) (spin n))" "recursion is not structural")
;; match on a computed value: an auxiliary define closed over the context. It computes in proofs;
;; it covers the cases; it does not hide a call to the define in progress.
(check-string "(claim mx-neg (→ Bool Bool))
(define (mx-neg b) (match b (true false) (false true)))
(claim mx-zero? (→ Nat Bool Bool))
(define (mx-zero? n b)
  (let ((m (mx-neg b)))
    (match* (n m)
      ((zero true) true)
      ((_ _) false))))
(claim mx-proof (≡ (mx-zero? 0 false) true))
(define mx-proof refl)")
(rejects "(claim mx-missing (→ Bool Bool))
(define (mx-missing b) (match (mx-neg b) (true true)))" "missing case")
(rejects "(claim mx-spin (→ Nat Nat))
(define (mx-spin n) (match (mx-neg true) (true (mx-spin n)) (false 0)))" "cannot call mx-spin")
(rejects "(claim mx-free Type)
(define mx-free (≡ (match true (true false) (false true)) false))" "annotate it with the")
(rejects "(claim wrong (≡ 1 2))
(define wrong refl)" "expected")
(rejects "(claim head-of-empty (→ (Vec A 0) A))
(define (head-of-empty nil) nil)" "expected")
(rejects "(extern lie : ⊥ nope)" "reserved to the standard library")
(rejects "(claim theft Dir)
(define theft (%host-dir \"/etc\"))" "reserved to the core")
(rejects "(claim different (≡ \"a\" \"b\"))
(define different refl)" "expected")
(parameterize ([privileged #t])
  (rejects "(extern lies : (→ Dir ⊥) Directory.nope)" "opaque engine type")
  (rejects "(extern observes : (→ Dir String) Directory.name)" "opaque engine type"))

;; --- plan ---

(define dir (format "~a/disegno-test-dir" (or (getenv "TMPDIR") "/tmp")))
(check-string (format "
(claim gen-config (→ Dir Dir))
(define (gen-config src) (with-file src /config/app.toml \"port = 8080\\n\"))

(claim main (Π ((src (Host ~s))) (Export Dir)))
(define (main src) (replace ~s (put (with-file empty /README \"hello\\n\") /cfg (gen-config src))))"
  (string-append dir "/in") (string-append dir "/out")))

(define dry (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch))))))
(assert (contains? dry "directory { withNewFile(path: \"/README\", contents: \"hello\\n\", permissions: 420) { withDirectory(path: \"/cfg\", source: \"<host { directory(path:"))
(assert (contains? dry "withNewFile(path: \\\"/config/app.toml\\\""))
(assert (contains? dry "} }>\") { export(path:"))
(assert (contains? dry "wipe: true"))

;; Container: the host directory goes into the container, a command processes it, the result comes out.
(check-string (format "
(claim build (Π ((src (Host ~s))) (Export Dir)))
(define (build src)
  (replace ~s
           (pipe (container)
                 (from \"alpine\")
                 (with-dir /w src)
                 (with-workdir /w)
                 (with-exec (list \"sh\" \"-c\" \"cat data.txt data.txt > double.txt\"))
                 (dir-of /w))))"
  (string-append dir "/in") (string-append dir "/out2")))
(define dry2 (plan->graphql (plan (lambda (ch) (format "<~a>" (plan->graphql ch))) 'build)))
(assert (contains? dry2 "container { from(address: \"alpine\") { withDirectory(path: \"/w\", source: \"<host"))
(assert (contains? dry2 "withExec(args: [\"sh\", \"-c\", \"cat data.txt data.txt > double.txt\"]) { directory(path: \"/w\")"))
(rejects "(claim mixed (List String))
(define mixed (list \"a\" 1))" "expected")
(rejects "(claim pipe Dir)
(define pipe empty)" "reserved word")
(check-string "(claim image-list (≡ (images (pipe (container) (from \"a\") (with-dir /w (dir-of (from container \"b\") root))))
                   (list \"a\" \"b\")))
(define image-list auto)")
(rejects "(claim must-pin (All pinned? (images (from container \"alpine\"))))
(define must-pin auto)" "auto: no proof of (Holds pinned? \"alpine\")")
(rejects "(claim wrong-branch (All pinned? (images (branch (Directory.exists empty /x) (from container \"a@sha256:4bcff63911fcb4448bd4fdacec207030997caf25e9bea4045fa6c8c44de311d1\") (from container \"b\")))))
(define wrong-branch auto)" "auto: no proof of")
(rejects "(claim under App)
(define under (app \"api\" prod 2 auto))" "auto: the proposition reduces to ⊥")
(rejects "(claim wrong-auto (≡ (+ 1 1) 3))
(define wrong-auto auto)" "expected")
(check-string "(claim api-name (≡ (App.name api) \"api\"))
(define api-name auto)")
(check-string "(claim twice (→ Nat Nat))
(define (twice n) (+ n n))
(claim eight (≡ (pipe 2 twice twice) 8))
(define eight refl)")

;; branch: the condition is a test in the container; both branches are in the plan.
(check-string (format "
(claim test-in (→ Dir String Container))
(define (test-in src file) (pipe (container) (from \"alpine\") (with-dir /w src) (try-exec (list \"test\" \"-f\" file))))

(claim outcome (→ (Remote Bool) Dir))
(define (outcome c) (branch c (with-file empty /outcome \"passes\\n\") (with-file empty /outcome \"fails\\n\")))

(claim verify (Π ((src (Host ~s))) (Export Dir)))
(define (verify src)
  (replace ~s (put (outcome (passes? (test-in src \"/w/data.txt\")))
                   /missing (outcome (exists? src /missing.txt)))))"
  (string-append dir "/in") (string-append dir "/out3")))
(define plans (all-plans 'verify))
(assert (= (length plans) 4))
(assert (contains? (plan->graphql (car (car (car (car plans)))))
                   "withExec(args: [\"test\", \"-f\", \"/w/data.txt\"], expect: ANY) { exitCode }"))
(assert (equal? (map (lambda (p) (map cdr (car p))) plans) '((#t #t) (#t #f) (#f #t) (#f #f))))
(rejects "(claim confused (→ (Remote Bool) Dir))
(define (confused c) (if c empty empty))" "expected")
(rejects "(claim choice (→ Bool Dir))
(define (choice b) (branch b empty empty))" "expected")

;; Dagger looks at the files' contents: observations like passes?, the text does not come back to the language.
(check-string (format "
(claim content (Π ((src (Host ~s))) (Export Dir)))
(define (content src)
  (let ((f (file-of src /data.txt)))
    (replace ~s (pipe empty
                      (put /include (outcome (includes? f \"data\")))
                      (put /absent (outcome (includes? f \"absent\")))
                      (put /regex (outcome (matches? f \"^d.t+a$\")))
                      (put /empty-file (outcome (empty? f)))
                      (put /same (outcome (same-content? f f)))))))"
  (string-append dir "/in") (string-append dir "/out4")))
(assert (= (length (all-plans 'content)) 32))

;; Effects in sequence: then realizes in order, apply is an effect outside the cache (a new
;; variable on each run, right before the command), skip does nothing.
(check-string (format "
(claim sequence (Export Dir))
(define sequence
  (begin
    (apply (from (container) \"alpine\") (list \"sh\" \"-c\" \"echo effect\"))
    skip
    (overlay ~s (with-file empty /after \"yes\\n\"))))"
  (string-append dir "/out5")))
(let ([es (exits resolve-dry 'sequence)])
  (assert (= (length es) 2))
  (assert (contains? (plan->graphql (car es)) "withEnvVariable(name: \"DISEGNO_RUN\", value: \"<run>-"))
  (assert (contains? (plan->graphql (car es)) "\") { withExec(args: [\"sh\", \"-c\", \"echo effect\"]) { exitCode }"))
  (assert (contains? (plan->graphql (cadr es)) "export(path:")))
;; Outside the cache: two runs give DISEGNO_RUN different values, so for Dagger the command
;; is another; the construction before the variable stays the same, and stays cached.
(let ([a (parameterize ([run-id "1"]) (plan->graphql (car (exits resolve-dry 'sequence))))]
      [b (parameterize ([run-id "2"]) (plan->graphql (car (exits resolve-dry 'sequence))))])
  (assert (not (string=? a b)))
  (assert (contains? a "value: \"1-")) (assert (contains? b "value: \"2-")))
;; And within the same run two identical fresh commands stay two: different values.
(check-string "(claim run-twice (Export Dir))
(define run-twice
  (begin
    (apply (from (container) \"alpine\") (list \"true\"))
    (apply (from (container) \"alpine\") (list \"true\"))))")
(let ([es (exits resolve-dry (quote run-twice))]) (assert (not (string=? (plan->graphql (car es)) (plan->graphql (cadr es))))))
(rejects "(claim inside Container)
(define inside (with-dir (from (container) \"a\") /x (overlay \"o\" empty)))" "expected")

;; Secrets: (Host-secret "NAME") in the signature, read from an environment variable. The plan names
;; the variable, never the value; the container gets it with with-secret-variable.
(check-string (format "
(claim secret-test (Π ((s (Host-secret \"PATH\"))) (Export Dir)))
(define (secret-test s)
  (branch (probe (with-secret-variable (from (container) \"alpine\") \"S\" s) (list \"sh\" \"-c\" \"test -n \\\"$S\\\"\"))
          (overlay ~s (with-file empty /outcome \"received\\n\"))
          (overlay ~s (with-file empty /outcome \"empty-file\\n\"))))
(claim bad-secret (Π ((s (Host-secret \"1 X\"))) (Export Dir)))
(define (bad-secret s) skip)"
  (string-append dir "/out6") (string-append dir "/out6")))
(let ([p (plan->graphql (cadr (car (cdr (car (all-plans 'secret-test))))))])
  (assert (contains? p "withSecretVariable(name: \"S\", secret: \"<secret(uri: \\\"env://PATH\\\")>\")"))
  (assert (not (contains? p (getenv "PATH")))))
(assert (contains? (guard (e [#t (condition-message e)]) (all-plans 'bad-secret) "") "is not the name of an environment variable"))
(rejects "(claim read-env String)
(define read-env (Query.secret \"env://HOME\"))" "unknown name")

;; re?: the match is against the whole string; it terminates even on patterns repeating the empty one.
(for-each (lambda (c) (unless (eq? (re? (car c) (cadr c)) (caddr c))
                        (error 'test (format "re? ~s ~s: expected ~a" (car c) (cadr c) (caddr c)))))
  '(("abc" "abc" #t) ("abc" "abcd" #f) ("a.c" "axc" #t) ("[a-z]+" "hello" #t) ("[a-z]+" "Hello" #f)
    ("[^0-9]*" "abc" #t) ("[^0-9]*" "a1" #f) ("\\d{3}" "123" #t) ("\\d{3}" "12" #f) ("a{2,}" "aaaa" #t)
    ("a{2,3}" "aaaa" #f) ("(ab|cd)+" "abcdab" #t) ("(ab|cd)+" "abc" #f) ("colou?r" "color" #t)
    ("\\w+@\\w+\\.it" "x_1@dominio.it" #t) ("(a*)*" "aaaa" #t) ("(a*)*b" "aaaa" #f) ("(a?){3}" "" #t)
    ("[a-z0-9][a-z0-9.-]{1,61}[a-z0-9]" "my-bucket.logs" #t) ("[a-z0-9][a-z0-9.-]{1,61}[a-z0-9]" "-bucket" #f)
    ("a]" "a]" #t) ("" "" #t) ("" "x" #f)))
(for-each (lambda (p) (assert (guard (e [(message-condition? e) (contains? (condition-message e) "malformed")]) (re? p "x") #f)))
          '("(" "a)" "[a" "*a" "a{2" "a{3,1}" "[z-a]"))
(check-string "(claim logs-bucket Bucket)
(define logs-bucket \"my-app.logs\")")
(rejects "(claim bad-bucket Bucket)
(define bad-bucket \"My_Bucket\")" "«My_Bucket» is not a valid Bucket")

;; AWS: the pinned CLI, with credentials as secrets; live it answers, without touching AWS.
(check-string (format "
(claim cli-aws (Π ((s (Host-secret \"PATH\"))) (Export Dir)))
(define (cli-aws s)
  (branch (probe (cli (aws s s \"eu-west-1\" cloud)) (list \"sh\" \"-c\" \"aws --version && test -n \\\"$AWS_ACCESS_KEY_ID\\\" && test \\\"$AWS_DEFAULT_REGION\\\" = eu-west-1\"))
          (overlay ~s (with-file empty /outcome \"answers\\n\"))
          (overlay ~s (with-file empty /outcome \"no\\n\"))))"
  (string-append dir "/out7") (string-append dir "/out7")))
(rejects "(claim r Region)
(define r \"eu-west-9\")" "«eu-west-9» is not a valid Region")

;; LocalStack as a service: the real Parameter Store, emulated. Write, then ask; the service is
;; the same for the whole session. Live only with DISEGNO_TEST_KEY (the shell exports it).
(check-string (format "
(claim outcome-ls (→ String (Export Dir)))
(define (outcome-ls t) (overlay ~s (with-file empty /outcome t)))
(claim with-localstack (Π ((k (Host-secret \"DISEGNO_TEST_KEY\"))) (Export Dir)))
(define (with-localstack k)
  (begin
    (start localstack)
    (let ((a (aws k k \"eu-west-1\" (emulated localstack))))
      (begin
        (put-parameter a /app/test/port \"5432\")
        (put-secure-parameter a /app/test/password k)
        (branch (parameter-is? a /app/test/port \"5432\")
                (branch (parameter-is? a /app/test/port \"9999\")
                        (outcome-ls \"mixes up the values\\n\")
                        (branch (parameter-exists? a /app/test/password)
                                (outcome-ls \"scritto\\n\")
                                (outcome-ls \"password missing\\n\")))
                (outcome-ls \"port not written\\n\"))))))"
  (string-append dir "/out8")))
(assert (= (length (all-plans 'with-localstack)) 4))
(check-string (format "
(claim outcome-s3 (→ String (Export Dir)))
(define (outcome-s3 t) (overlay ~s (with-file empty /outcome t)))
(claim test-bucket Bucket)
(define test-bucket \"disegno-test\")
(claim with-s3 (Π ((k (Host-secret \"DISEGNO_TEST_KEY\"))) (Export Dir)))
(define (with-s3 k)
  (begin
    (start localstack)
    (let ((a (aws k k \"eu-west-1\" (emulated localstack))))
      (begin
        (make-bucket a test-bucket)
        (s3-sync a (with-file empty /index.html \"<h1>hello</h1>\\n\") test-bucket /site)
        (branch (s3-includes? a test-bucket /site/index.html \"hello\")
                (branch (s3-exists? a test-bucket /site/missing.html)
                        (outcome-s3 \"finds what is not there\\n\")
                        (outcome-s3 \"published\\n\"))
                (outcome-s3 \"page absent\\n\"))))))"
  (string-append dir "/out10")))
;; Plan parameters: (Host-env "NAME" "default"), read from the environment when the plan is
;; built. They decide the ifs too: the plan is a function of its parameters.
(check-string (format "
(claim param (Π ((t (Host-env \"DISEGNO_TEST_TAG\" \"1.0\")) (k (Host-env \"DISEGNO_TEST_KIND\" \"release\"))) (Export Dir)))
(define (param t k)
  (if (same? k \"rollback\")
      (overlay ~s (with-file empty /rollback t))
      (overlay ~s (with-file empty /release t))))
(claim bad-param (Π ((t (Host-env \"1 X\" \"\"))) (Export Dir)))
(define (bad-param t) skip)"
  (string-append dir "/out12") (string-append dir "/out12")))
(let ([p (lambda () (plan->graphql (plan resolve-dry 'param)))])
  (assert (contains? (p) "withNewFile(path: \"/release\", contents: \"1.0\""))
  (putenv "DISEGNO_TEST_KIND" "rollback") (putenv "DISEGNO_TEST_TAG" "10.0.42")
  (assert (contains? (p) "withNewFile(path: \"/rollback\", contents: \"10.0.42\""))
  (putenv "DISEGNO_TEST_KIND" "") (putenv "DISEGNO_TEST_TAG" ""))   ; empty counts as absent
(assert (contains? (guard (e [#t (condition-message e)]) (plan resolve-dry 'bad-param) "") "is not the name of an environment variable"))
;; (Host-choice "NAME" Type default): the constructor with that name; an unknown name stops the
;; plan. (fail "msg"): dry an event of the plan, live the error.
(check-string (format "
(data Stage (development) (production))
(claim per-stage (Π ((a (Host-choice \"DISEGNO_TEST_STAGE\" Stage development))) (Export Dir)))
(define (per-stage a)
  (match a
    (development (overlay ~s (with-file empty /development \"\")))
    (production (fail \"no prod from here\"))))
(claim bad-choice (Π ((a (Host-choice \"DISEGNO_TEST_STAGE\" Nat zero))) (Export Dir)))
(define (bad-choice a) skip)"
  (string-append dir "/out12")))
(assert (contains? (plan->graphql (plan resolve-dry 'per-stage)) "/development"))
(putenv "DISEGNO_TEST_STAGE" "production")
(assert (equal? (cdr (car (all-plans 'per-stage))) '((fails "no prod from here"))))
(putenv "DISEGNO_TEST_STAGE" "staging")
(assert (contains? (guard (e [#t (condition-message e)]) (plan resolve-dry 'per-stage) "") "«staging» is not one of development, production"))
(assert (contains? (guard (e [#t (condition-message e)]) (plan resolve-dry 'bad-choice) "") "constructors without arguments only"))
(putenv "DISEGNO_TEST_STAGE" "")
(check-string "(claim stage-name (≡ (Stage.name production) \"production\"))
(define stage-name refl)")   ; D.name, the inverse of Host-choice, generated with the data
;; A stuck value (here the credentials read from Secrets Manager) remembers the item it was born
;; in, and takes it back when the runner unsticks it: the ECR steps belong to work, not to main.
(check-string "(import aws delivery)
(claim account-of (→ Bool Account))
(define (account-of b) (match b (true \"111111111111\") (false \"222222222222\")))
(claim other-aws (→ Aws Aws))
(define (other-aws boot) (aws (secrets-manager-key-first boot (list \"a\") \"username\" \"u\") (secrets-manager-key-first boot (list \"a\") \"password\" \"p\") \"eu-west-1\" cloud))
(claim work (→ Aws Bool (Export Dir)))
(define (work boot b) \"publishes\"
  (let ((reg (ecr (other-aws boot) (account-of b))))
    (unless (Registry.has? reg \"repo\" \"tag\") (Registry.push reg (pipe (container) (from \"alpine\")) \"repo\" \"tag\"))))
(claim labelled (Π ((id (Host-secret \"AWS_ACCESS_KEY_ID\")) (key (Host-secret \"AWS_SECRET_ACCESS_KEY\")) (s (Host-env \"DISEGNO_TEST_S\" \"x\"))) (Export Dir)))
(define (labelled id key s) (work (aws id key \"eu-west-1\" cloud) (same? s \"x\")))")
(assert (equal? (map (lambda (ch) (item-of (last-of (filter (lambda (s) (eq? (car s) 'withExec)) ch))))
                     (parameterize ([observe (lambda (ch) #f)]) (exits resolve-dry 'labelled)))
                '(work work)))

;; otherwise: if a fails b is realized, then it fails anyway. Dry the plan shows b after the
;; mark «if something before fails». For Before, b counts as if a had failed right away.
(check-string (format "
(claim with-fallback (Export Dir))
(define with-fallback
  (otherwise (begin
               (overlay ~s (with-file empty /before \"yes\\n\"))
               (apply (from (container) \"alpine\") (list \"sh\" \"-c\" \"exit 3\")))
             (overlay ~s (with-file empty /fallback \"yes\\n\"))))
(claim release-or-report (→ Dir (Export Dir)))
(define (release-or-report src)
  (otherwise (when (passes? (try-exec (with-dir (from (container) \"alpine\") /w src) (list \"true\")))
               (apply (from (container) \"alpine\") (list \"echo\" \"deploy\")))
             (overlay \"report\" (with-file empty /failed \"yes\\n\"))))
(claim guarded-deploy (Π ((src Dir)) (Before test? apply? (release-or-report src))))
(define (guarded-deploy src) auto)"
  (string-append dir "/out13") (string-append dir "/out13")))
(assert (equal? (map car (cdr (car (all-plans 'with-fallback)))) '(output output otherwise output)))
;; An apply as a fallback is not guarded by the test: Before sees it, because b counts alone.
(rejects "(claim unguarded-fallback (Π ((src Dir)) (Before test? apply? (otherwise (release-or-report src) (apply (from (container) \"alpine\") (list \"echo\" \"report\"))))))
(define (unguarded-fallback src) auto)" "auto")

;; Secrets read at run time: Secrets Manager on LocalStack. The secret is created (here, in plain
;; text: it is a test), then a container gets it from secrets-manager-key and compares it. The
;; consumer's plan shows the command that reads it, never the value.
(check-string (format "
(claim outcome-sm (→ String (Export Dir)))
(define (outcome-sm t) (overlay ~s (with-file empty /outcome t)))
(claim with-secrets (Π ((k (Host-secret \"DISEGNO_TEST_KEY\"))) (Export Dir)))
(define (with-secrets k)
  (begin
    (start localstack)
    (let ((a (aws k k \"eu-west-1\" (emulated localstack))))
      (begin
        (apply (cli a) (list \"aws\" \"secretsmanager\" \"create-secret\" \"--name\" \"cicd/test/argocd\"
                             \"--secret-string\" \"{\\\"host\\\":\\\"argocd.example\\\",\\\"token\\\":\\\"t0k\\\"}\"))
        (apply (cli a) (list \"aws\" \"secretsmanager\" \"create-secret\" \"--name\" \"cicd/test/key\"
                             \"--secret-binary\" \"dW5vCmR1ZQo=\"))
        (branch (probe (pipe (from (container) \"alpine\")
                             (with-secret-variable \"T\" (secrets-manager-key a \"cicd/test/argocd\" \"token\"))
                             (with-secret-variable \"K\" (secrets-manager-first a (list \"cicd/test/absent\" \"cicd/test/key\") \"key\"))
                             ;; the secret is there but the key is not: the default holds, and nothing else
                             (with-secret-variable \"D\" (secrets-manager-key-first-or a (list \"cicd/test/argocd\") \"server\" \"fallback\" \"argocd-server\")))
                       (list \"sh\" \"-c\" \"test \\\"$T\\\" = t0k && test \\\"$K\\\" = \\\"$(printf 'uno\\\\ndue')\\\" && test \\\"$D\\\" = fallback\"))
                (outcome-sm \"received\\n\")
                (outcome-sm \"different\\n\"))))))"
  (string-append dir "/out11")))
(let* ([evs (cdr (car (all-plans 'with-secrets)))]
       [obs (plan->graphql (cadr (find (lambda (e) (eq? (car e) 'if)) evs)))])
  (assert (contains? obs "secretFrom(name: \\\"cicd/test/argocd:token\\\", args: [\\\"sh\\\", \\\"-c\\\""))   ; the name and the command, inside the GraphQL string
  (assert (contains? obs "\\\"cicd/test/argocd\\\", \\\"token\\\"]"))
  (assert (not (contains? obs "argocd.example"))))                   ; the secret's value is not in the plan

;; delivery: Registry, Gitops and Deployer, with their implementations. A registry and a git server
;; as services, to try push, «is it there?», clone, kustomize, commit and push without external services.
(check-string (format "
(claim outcome-d (→ Segment String (Export Dir)))
(define (outcome-d p t) (overlay ~s (with-file empty (/ root p) t)))
(claim test-image Container)
(define test-image (pipe (container) (from \"busybox@sha256:bdf57e528e45e4433820e045b29b4597825a1c9e38353532d90a01445013f82e\")))
(claim with-registry (Export Dir))
(define with-registry
  (begin
    (start registry-service)
    (Registry.push (local-registry registry-service) test-image \"prova/app\" \"v1\")
    (branch (Registry.has? (local-registry registry-service) \"prova/app\" \"v1\")
            (outcome-d \"registry\" \"pushed\\n\")
            (outcome-d \"registry\" \"absent\\n\"))))
(claim git-server Service)
(define git-server
  (pipe git-tool
        (with-exec (list \"sh\" \"-c\" \"apk add -q --no-cache git-daemon && git init -q --bare -b main /srv/app.git && git init -q -b main /tmp/w && cd /tmp/w && mkdir -p console/test/app && printf 'resources: []\\\\n' > console/test/app/kustomization.yaml && git add -A && git -c user.name=t -c user.email=t@t commit -qm init && git push -q /srv/app.git main\"))
        (with-exposed-port 9418)
        (with-default-args (list \"git\" \"daemon\" \"--reuseaddr\" \"--export-all\" \"--enable=receive-pack\" \"--base-path=/srv\" \"/srv\"))
        (as-service false)))
(claim test-repo Gitops)
(define test-repo (kustomize-gitops \"git://git:9418/app.git\" \"main\" anonymous (through \"git\" git-server) (author \"Disegno\" \"ci@disegno.invalid\")))
(claim with-gitops (Export Dir))
(define with-gitops
  (begin
    (start git-server)
    (Gitops.set-image test-repo (list \"console/test/app\") \"registry:5000/prova/app:v2\" \"image v2\")
    (branch (probe (with-dir test-image /r (clone \"git://git:9418/app.git\" \"main\" anonymous (through \"git\" git-server)))
                   (list \"grep\" \"-q\" \"newTag: v2\" \"/r/console/test/app/kustomization.yaml\"))
            (outcome-d \"gitops\" \"updated\\n\")
            (outcome-d \"gitops\" \"unchanged\\n\"))))
(claim with-argocd (Π ((s (Host-secret \"PATH\"))) (Export Dir)))
(define (with-argocd s)
  (branch (probe (argocd-cli (argocd (public \"argocd.invalid\") (token s) false)) (argocd-args (list \"version\" \"--client\")))
          (outcome-d \"argocd\" \"answers\\n\")
          (outcome-d \"argocd\" \"no\\n\")))
(claim test-release (→ Secret (Export Dir)))
(define (test-release s)
  (begin
    (Gitops.set-image test-repo (list \"console/test/app\") \"registry:5000/prova/app:v3\" \"v3\")
    (Deployer.deploy (argocd-deployer (argocd (public \"argocd.invalid\") (token s) false) 300) \"app\")))
(claim sync-after-push (Π ((s Secret)) (Precedes (git-command? \"push\") (argocd-command? \"sync\") (test-release s))))
(define (sync-after-push s) auto)"
  (string-append dir "/out14")))
(rejects "(claim push-after-sync (Π ((s Secret)) (Precedes (argocd-command? \"sync\") (git-command? \"push\") (test-release s))))
(define (push-after-sync s) auto)" "auto")

;; A Dockerfile build with an argument and a secret by name: ARG VERSION and
;; RUN --mount=type=secret,id=ssh-key see them.
(check-string (format "
(claim context Dir)
(define context (with-file empty /Dockerfile \"FROM busybox@sha256:bdf57e528e45e4433820e045b29b4597825a1c9e38353532d90a01445013f82e\\nARG VERSION\\nARG DISEGNO_RUN\\nRUN --mount=type=secret,id=ssh-key mkdir /out && test \\\"$(cat /run/secrets/ssh-key)\\\" = key && echo read $VERSION > /out/outcome\\n\"))
(claim with-dockerfile (Export Dir))
(define with-dockerfile
  (overlay ~s (dir-of (build-dockerfile context \"Dockerfile\" (list (build-arg \"VERSION\" \"1.2\"))
                                        (list (secret-from (from (container) \"busybox@sha256:bdf57e528e45e4433820e045b29b4597825a1c9e38353532d90a01445013f82e\") (list \"echo\" \"key\") \"ssh-key\")))
                      /out)))"
  (string-append dir "/out15")))
;; With secrets the build also gets DISEGNO_RUN; without, the arguments stay as written.
(let ([p (plan->graphql (cadr (cadr (car (all-plans 'with-dockerfile)))))])
  (assert (contains? p "{name: \"VERSION\", value: \"1.2\"}, {name: \"DISEGNO_RUN\", value: \"<run>\"}")))

;; Promoted optional arguments: a file's permissions, filter's globs, a service's entrypoint.
(check-string (format "
(claim d9 Dir)
(define d9 (pipe empty (with-executable /run.sh \"#!/bin/sh\\necho ok\\n\") (with-file /note.txt \"x\\n\")))
(claim filters (Export Dir))
(define filters
  (branch (passes? (try-exec (with-dir (from (container) \"alpine\") /w d9) (list \"sh\" \"-c\" \"test -x /w/run.sh && test ! -x /w/note.txt\")))
          (overlay ~s (only d9 (list \"*.sh\")))
          (overlay ~s (with-file empty /error \"permissions\\n\"))))"
  (string-append dir "/out9") (string-append dir "/out9")))
(let ([p (plan->graphql (cadr (cadr (cdr (car (all-plans 'filters))))))])
  (assert (contains? p "withNewFile(path: \"/run.sh\", contents: \"#!/bin/sh\\necho ok\\n\", permissions: 493)"))
  (assert (contains? p "filter(exclude: [], include: [\"*.sh\"])")))
(assert (contains? (plan->graphql (chain (ev '() '(glob localstack)) resolve-dry)) "asService(useEntrypoint: true)"))
;; In the report a long library script reads from its arguments; a short one stays.
(assert (string=? (show-args (list "sh" "-c" (make-string 130 #\x) "sh" "MODE" "cicd/deploy")) "sh -c … sh MODE cicd/deploy"))
(assert (string=? (show-args (list "sh" "-c" "echo effect")) "sh -c \"echo effect\""))

;; What a plan writes: only the put-parameters, not the other effects.
(check-string "(claim written-params (Π ((a Aws)) (≡ (parameters (begin
                                             (put-parameter a /app/x \"1\")
                                             (apply (from (container) \"b\") (list \"echo\"))))
                               (list /app/x))))
(define (written-params a) auto)")
(assert (contains? (plan->graphql (car (car (car (car (all-plans 'content))))))
                   "withExec(args: [\"grep\", \"-qF\", \"data\", \"/f\"], expect: ANY) { exitCode }"))

;; Externs generated from the schema, used directly: Nat and objects by ID in the arguments.
(check-string "
(claim serve (Π ((src (Host \"/x\"))) (Export Dir)))
(define (serve src)
  (overlay \"out\" (pipe (Query.git \"https://example.com/r.git\") (GitRepository.branch \"main\") GitRef.tree
                       (put /port (dir-of (Container.with-exposed-port (container) 8080) root)))))")
(define dry3 (plan->graphql (plan resolve-dry 'serve)))
(assert (contains? dry3 "git(url: \"https://example.com/r.git\") { branch(name: \"main\") { tree {"))
(assert (contains? dry3 "withExposedPort(port: 8080)"))

;; Order properties: they hold for every input, because effects does not go into directories.
(check-string "
(claim img (→ Dir Container))
(define (img src) (pipe (container) (from \"alpine\") (with-dir /app src)))
(claim guarded (→ Dir (Export Dir)))
(define (guarded src)
  (branch (passes? (try-exec (from container \"alpine\") (list \"true\")))
          (branch (exists? src /VERSION) (publish (img src) \"r/app:1\") (overlay \"o\" src))
          (overlay \"o\" src)))
(claim order-ok (Π ((src Dir)) (Before test? publish? (guarded src))))
(define (order-ok src) auto)")
(rejects "(claim unguarded (Π ((src Dir)) (Before test? publish? (publish (img src) \"r/app:1\"))))
(define (unguarded src) auto)"
         "reduces to ⊥")
(rejects "(claim fake-test (Π ((src Dir)) (Before test? publish? (branch (exists? src /x) (publish (img src) \"r\") (overlay \"o\" src)))))
(define (fake-test src) auto)"
         "reduces to ⊥")
(rejects "(claim in-wrong-branch (Π ((src Dir)) (Before test? publish? (branch (passes? (img src)) (overlay \"o\" src) (publish (img src) \"r\")))))
(define (in-wrong-branch src) auto)"
         "reduces to ⊥")

;; Short names: the type of the first argument picks the method; without a method it is a root field.
(check-string "
(claim short (Π ((src (Host \"/x\"))) (Export Dir)))
(define (short src)
  (overlay \"out\" (pipe (container) (from \"alpine\") (with-mounted-cache /c (cache-volume \"k\"))
                       (directory root) (with-new-file /a \"b\" 420) (directory /sub))))")
(define dry4 (plan->graphql (plan resolve-dry 'short)))
(assert (contains? dry4 "withMountedCache(path: \"/c\", cache: \"<cacheVolume(key: \\\"k\\\")>\") { directory(path: \"/\") { withNewFile(path: \"/a\", contents: \"b\", permissions: 420) { directory(path: \"/sub\")"))
(rejects "(claim wrong-exec Dir)
(define wrong-exec (with-exec empty (list \"x\")))" "with-exec does not exist for")
(rejects "(claim pin Dir)
(define pin (Query.cache-volume \"k\"))" "unknown name")

;; Refined values and paths: the literal stays, the type changes; points do not add up.
(rejects "(claim c1 Container)
(define c1 (from container \"Golang:1.25\"))" "«Golang:1.25» is not a valid Image")
(rejects "(claim c2 Container)
(define c2 (from container \"golang:1.25@sha256:abc\"))" "is not a valid Image")
(rejects "(claim c3 Dir)
(define c3 (with-file empty /a/../b \"x\"))" "«..» is not a valid Segment")
(rejects "(claim c4 Abs)
(define c4 (/ /out /bin))" "expected Segment, found Abs")
(rejects "(claim c5 (⊑ /out /out/bin))
(define c5 auto)" "auto: no proof of (⊑ /out /out/bin)")
(check-string "(claim c6 Container)
(define c6 (from container \"ghcr.io/dagger/engine:v0.21.10\"))
(claim c7 (⊑ (/ /out \"hello\") /out))
(define c7 auto)
(claim c8 (≡ (let ((o /out)
                   (b (/ o \"x\"))) b) /out/x))
(define c8 auto)")

;; The affine space of paths: the difference exists only with the containment proof.
(check-string "
(claim vector (≡ (⊖ /out/bin/hello /out auto) \"bin/hello\"))
(define vector auto)
(claim sum (≡ (⊕ /out \"bin/hello\") /out/bin/hello))
(define sum auto)
(claim inherited-law (≡ (⊕ /out (⊖ /out/bin /out auto)) /out/bin))
(define inherited-law (Affine.law path-affine /out/bin /out auto))")
(rejects "(claim crooked Rel)
(define crooked (⊖ /out /src auto))" "auto: no proof of (⊑ /out /src)")
(rejects "(claim points Abs)
(define points (⊕ /out /bin))" "expected Rel, found Abs")

;; Regions: overlapping mounts in the same chain are rejected; in different chains they are not.
(check-string "
(claim disjoint (⋔ /src /go/pkg/mod))
(define disjoint auto)
(claim two-chains (Disjoint-mounts (pipe (container) (with-dir /w (dir-of (pipe (container) (with-dir /w empty)) /w)))))
(define two-chains auto)")
(rejects "(claim nested (⋔ /src /src/cache))
(define nested auto)" "auto: no proof of (⋔ /src /src/cache)")
(rejects "(claim overlapping (Π ((src Dir)) (Disjoint-mounts (pipe (container) (with-dir /src src) (with-mounted-cache /src/cache (cache-volume \"c\"))))))
(define (overlapping src) auto)"
         "auto: no proof")

;; Absurd patterns: only where no constructor is possible; they are not a loophole.
(rejects "(claim fake-absurd (¬ (≡ 0 0)))
(define (fake-absurd n)
  (match n
    (())))" "() is not absurd: refl is possible")
(rejects "(claim fake-absurd2 (¬ (⊑ /out/x /out)))
(define (fake-absurd2 n)
  (match n
    ((⊑-step ()))))" "() is not absurd")
(rejects "(claim direct-false ⊥)
(define (direct-false n)
  (match n
    (())))" "too many patterns")
(rejects "(claim true-negated (¬ (⊑ /out/x /out)))
(define true-negated auto)" "auto: no refutation of (⊑ /out/x /out)")

;; Literals of time, addresses and ports: malformed or out of space they are type errors.
(rejects "(claim t1 Instant)
(define t1 \"2026-13-01\")" "«2026-13-01» is not a valid Instant")
(rejects "(claim t2 Duration)
(define t2 \"5x\")" "«5x» is not a valid Duration")
(rejects "(claim t3 Ip)
(define t3 \"10.0.0.256\")" "«10.0.0.256» is not a valid Ip")
(rejects "(claim t4 Cidr)
(define t4 \"10.0.0.1/24\")" "«10.0.0.1/24» is not a valid Cidr")
(rejects "(claim t5 Container)
(define t5 (with-exposed-port (container) 70000))" "«70000» is not a valid Port")
(rejects "(claim t6 Instant)
(define t6 (⊕ day-start day-end))" "expected Duration, found Instant")
(check-string "(claim last-ip Ip)
(define last-ip \"255.255.255.255\")")
(rejects "(claim beyond Ip)
(define beyond (⊕ last-ip 1 auto))" "reduces to ⊥")      ; overflow is ruled out

;; The cookbook: every recipe is a program of its own, verified in a separate process with
;; check (types and theorems) and, if it has a main, plan (the dry plan). Never run: 03 publishes.
;; The book's chapters (book/) and the exercises' solutions (book/solutions/) are verified programs too.
(for-each
  (lambda (r)
    (let* ([path (at-root r)]
           [mode (if (contains? (call-with-input-file path get-string-all) "(claim main ") "plan" "check")])
      (unless (zero? (system (format "scheme --script ~a ~a ~a >/dev/null" (at-root "src/main.ss") mode path)))
        (error 'test (format "~a does not pass (~a)" r mode)))))
  (apply append
         (map (lambda (dir)
                (map (lambda (f) (string-append dir "/" f))
                     (sort string<? (filter (lambda (f) (let ([n (string-length f)]) (and (> n 8) (string=? (substring f (- n 8) n) ".disegno"))))
                                            (directory-list (at-root dir))))))
              '("cookbook" "book" "book/solutions"))))

;; When auto fails on a conjunction, the message points at the part that does not hold.
(rejects "(claim overlapping-subnets (Disjoint-subnets (list \"10.0.1.0/24\" \"10.0.2.0/24\" \"10.0.1.128/25\")))
(define overlapping-subnets auto)"
         "auto: no proof of (Cidr-apart \"10.0.1.0/24\" \"10.0.1.128/25\")")
(rejects "(claim repeated-ports (Distinct-ports (pipe (container) (with-exposed-port 80) (with-exposed-port 443) (with-exposed-port 80))))
(define repeated-ports auto)"
         "auto: no proof of (port≠ 80 80)")
(rejects "(claim nested-mounts (Disjoint-mounts (pipe (container) (with-dir /src empty) (with-mounted-cache /src/cache (cache-volume \"c\")))))
(define nested-mounts auto)"
         "auto: no proof of (⋔ /src/cache /src)")
;; Positions: file:line:col of the nearest expression.
(rejects "(claim ok Nat)
(define ok 1)
(claim evil Abs)
(define evil (⊕ /out /bin))" "<string>:4:22: /bin: expected Rel, found Abs")
;; An error does not stop the file; using a name whose signature is wrong adds no errors.
(rejects "(claim a Nat)
(define a zz)
(claim b Bool)
(define b 3)" "<string>:4:1: 3: expected Bool")
;; import: only the modules of lib/, by name; a path does not pass.
(rejects "(import ../tests/checks)" "is not a module name")
(rejects "(import nowhere)" "module nowhere does not exist")
;; builtin: only in the library, closed keys, once, of the right kind.
(rejects "(builtin nat Nat)" "builtin is reserved to the standard library")
(parameterize ([privileged #t])
  (rejects "(builtin integer Nat)" "unknown key integer")
  (rejects "(builtin nat Bool)" "nat is already bound to Nat"))
;; In signatures only variable-shaped names are generalized: Socket is not an implicit type.
(rejects "(claim f (→ Socket Nat))
(define (f _) 0)" "unknown name: Socket")
(assert (equal? (guard (e [#t (condition-message e)]) (check-string "(claim f (→ Nat \"x\"))
(define (f _) 0)
(claim g Nat)
(define g (f 1))") #f)
                "<string>:1:10: \"x\" is not a type"))

;; The LSP: a recorded session (initialize, opening with an error, fix, save, shutdown) read
;; by the server from stdin; the diagnostics appear and then empty out.
(let* ([frame (lambda (v) (let ([b (string->utf8 (json->string v))])
                            (string-append (format "Content-Length: ~a\r\n\r\n" (bytevector-length b)) (utf8->string b))))]
       [uri "file:///tmp/lsp-test.disegno"]
       [in "/tmp/disegno-lsp-in"] [out "/tmp/disegno-lsp-out"]
       [msg (lambda (method params . id) `(("jsonrpc" . "2.0") ,@(if (null? id) '() `(("id" . ,(car id)))) ("method" . ,method) ("params" . ,params)))])
  (call-with-output-file in
    (lambda (p)
      (for-each (lambda (m) (put-string p (frame m)))
        (list (msg "initialize" '(("capabilities" . (("x" . 1)))) 1)
              (msg "textDocument/didOpen" `(("textDocument" . (("uri" . ,uri) ("text" . "(import paths)
(claim evil Abs)
(define evil (⊕ /out /bin))
(claim worse Nat)
(define worse \"x\")
(claim hole (→ Nat Nat))
(define (hole n) (add1 TODO))
(claim web80 Port)
(define web80 80)
")))))
              (msg "textDocument/didChange" `(("textDocument" . (("uri" . ,uri))) ("contentChanges" . ,(vector '(("text" . "(import paths)
(claim beta Abs)
(define beta (⊕ /out \"bin\"))
(claim r (≡ 1 1))
(define r refl)
(claim double (→ Nat Nat))
(define (double n) (add1 (add1 n)))
"))))))
              (msg "textDocument/didSave" `(("textDocument" . (("uri" . ,uri)))))
              (msg "textDocument/hover" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 2) ("character" . 14)))) 3)
              (msg "textDocument/definition" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 4) ("character" . 11)))) 4)
              (msg "textDocument/definition" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 2) ("character" . 9)))) 5)
              (msg "textDocument/documentSymbol" `(("textDocument" . (("uri" . ,uri)))) 6)
              (msg "textDocument/completion" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 1) ("character" . 9)))) 7)
              (msg "completionItem/resolve" `(("label" . "beta") ("kind" . 3) ("data" . (("uri" . ,uri) ("position" . (("line" . 1) ("character" . 9)))))) 8)
              (msg "textDocument/hover" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 6) ("character" . 31)))) 9)
              (msg "textDocument/definition" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 6) ("character" . 31)))) 10)
              (msg "textDocument/completion" `(("textDocument" . (("uri" . ,uri))) ("position" . (("line" . 6) ("character" . 32)))) 11)
              (msg "shutdown" '(("x" . 1)) 2)
              (msg "exit" '(("x" . 1)))))) 'replace)
  (system (format "scheme --script ~a lsp < ~a > ~a" (at-root "src/main.ss") in out))
  (let ([r (call-with-input-file out get-string-all)])
    (assert (contains? r "\"capabilities\""))
    (assert (contains? r "\"range\":{\"start\":{\"line\":2,\"character\":21}"))
    (assert (contains? r "\"message\":\"/bin: expected Rel, found Abs\""))
    (assert (contains? r "\"range\":{\"start\":{\"line\":4,\"character\":0}"))   ; the second error too
    (assert (contains? r "\"id\":4,\"result\":[{\"uri\":\"file:///"))         ; refl: in the standard library
    (assert (contains? r "lib/prelude.disegno\",\"range\":{\"start\":{\"line\":6,"))
    (assert (contains? r (format "\"id\":5,\"result\":[{\"uri\":\"~a\",\"range\":{\"start\":{\"line\":2,\"character\":0}" uri)))   ; beta: its define
    (assert (contains? r "\"name\":\"beta\",\"kind\":12"))
    (assert (contains? r "\"name\":\"r\",\"kind\":12"))
    ;; completion: the prefix «be» gives the global beta and the form begin; resolve gives the type
    (assert (contains? r (format "{\"label\":\"beta\",\"kind\":3,\"data\":{\"uri\":\"~a\",\"position\":{\"line\":1,\"character\":9}}}" uri)))
    (assert (contains? r "{\"label\":\"begin\",\"kind\":14"))
    (assert (contains? r "\"id\":8,\"result\":{\"label\":\"beta\",\"kind\":3,\"data\":{\"uri\":\"file:///tmp/lsp-test.disegno\",\"position\":{\"line\":1,\"character\":9}},\"detail\":\"beta : Abs\"}"))
    ;; a local: its type, its binder, and offered first by completion
    (assert (contains? r "\"id\":9,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```disegno\\nn : Nat\\n```\"}}"))
    (assert (contains? r (format "\"id\":10,\"result\":[{\"uri\":\"~a\",\"range\":{\"start\":{\"line\":6,\"character\":16}" uri)))
    (assert (contains? r "\"id\":11,\"result\":{\"isIncomplete\":false,\"items\":[{\"label\":\"n\",\"kind\":3"))
    (assert (contains? r "\"diagnostics\":[]"))
    ;; a TODO: on the hole, as information, with its context and goal
    (assert (contains? r "{\"range\":{\"start\":{\"line\":6,\"character\":23},\"end\":{\"line\":6,\"character\":27}},\"severity\":3,\"source\":\"disegno\",\"message\":\"TODO\\n  n : Nat\\n  ──────────\\n  Nat\"}"))
    ;; an unknown name: on the name, with the module that declares it
    (assert (contains? r "{\"range\":{\"start\":{\"line\":7,\"character\":13},\"end\":{\"line\":7,\"character\":17}},\"severity\":1,\"source\":\"disegno\",\"message\":\"unknown name: Port, it is in net: (import net)\"}"))
    (assert (contains? r "\"id\":3,\"result\":{\"contents\":{\"kind\":\"markdown\",\"value\":\"```disegno\\nAbs.⊕ : (→ Abs Rel Abs)\\n"))   ; and the other variants of ⊕
    (assert (contains? r "\"id\":2,\"result\":null"))))

;; In patterns a symbol is a constructor only if it is one of the expected type: step, port, root…
;; stay variables where the type is another. Coverage uses the same resolution.
(check-string "
(claim add-step (→ Nat (→ Nat Nat) Nat))
(define (add-step port n)
  (match n
    (step (step port))))
(claim use-step (≡ (add-step 2 add1) 3))
(define use-step auto)")
(rejects "(claim missing-step (→ Rel Nat))
(define (missing-step n)
  (match n
    (here 0)))" "missing case")

;; The log stream reorders by instant: a stderr packet delivered late goes to its place.
(let ([p (open-output-string)])
  (define (record t s)
    `(("timeUnixNano" . ,(number->string t)) ("body" ("stringValue" . ,s)) ("attributes" (("key" . "stdio.stream")))))
  (set! log-port p)
  (for-each (lambda (t s) (on-log (record t s))) '(100 300 200) '("A\n" "C\n" "B\n"))
  (flush! (- (now-ns) window))                          ; just arrived: they wait
  (assert (string=? (get-output-string p) ""))
  (flush! +inf.0)
  (assert (string=? (get-output-string p) "A\nB\nC\n"))
  (set! log-port #f))

;; --- live ---















(define (run-capturing entry)                                    ; → (message . output) of run entry
  (let* ([msg #f]
         [out (with-output-to-string
                (lambda () (set! msg (guard (e [(message-condition? e) (condition-message e)]) (run entry) #f))))])
    (cons msg out)))

(when (getenv "DAGGER_SESSION_PORT")
  (system (format "rm -rf ~a && mkdir -p ~a/in && echo data > ~a/in/data.txt" dir dir dir))
  (submit-leaf (plan (lambda (ch) (submit-leaf (append ch '((id)))))))
  (for-each (lambda (f) (assert (file-exists? (string-append dir "/out/" f))))
            '("README" "cfg/data.txt" "cfg/config/app.toml"))
  (submit-leaf (plan (lambda (ch) (submit-leaf (append ch '((id))))) 'build))
  (assert (string=? (call-with-input-file (string-append dir "/out2/double.txt") get-string-all) "data\ndata\n"))
  (run 'verify)
  (assert (string=? (call-with-input-file (string-append dir "/out3/outcome") get-string-all) "passes\n"))
  (assert (string=? (call-with-input-file (string-append dir "/out3/missing/outcome") get-string-all) "fails\n"))
  (run (quote content))
  (for-each (lambda (p e) (assert (string=? (call-with-input-file (string-append dir "/out4/" p "/outcome") get-string-all) e)))
            (quote ("include" "absent" "regex" "empty-file" "same")) (quote ("passes\n" "fails\n" "passes\n" "fails\n" "passes\n")))
  ;; A failed step says where it is in the source, with and without the report (DISEGNO_LOGS, as in
  ;; CI: one line per item). First without: Chez cannot unset an environment variable.
  ;; live-direct has new commands on each run, so it is not cached and its lines come through the stream.
  (putenv "GITHUB_ACTIONS" "") (putenv "GITLAB_CI" "")       ; the neutral format, in CI too
  (let ([n (time-nanosecond (current-time))])
    (check-string (format "(claim broken (→ (Export Dir)))
(define broken
  (overlay \"broken\" (pipe (container) (from \"alpine\")
                         (with-exec (list \"sh\" \"-c\" \"echo A; sleep 0.3; echo B >&2; sleep 0.3; echo C\"))
                         (with-exec (list \"sh\" \"-c\" \"echo evil >&2; exit 3\")) (dir-of /tmp))))
(claim prepare Container)
(define prepare \"sets up the environment\" (pipe (container) (from \"alpine\") (with-exec (list \"sh\" \"-c\" \"echo prep~a\"))))
(claim live-direct (Π ((src (Host ~s))) (Export Dir)))
(define (live-direct src)
  (overlay \"broken\" (pipe prepare (with-dir /w src)
                         (with-exec (list \"sh\" \"-c\" \"echo A~a; sleep 0.05; echo B >&2; sleep 0.05; echo C\"))
                         (with-exec (list \"sh\" \"-c\" \"echo evil~a >&2; exit 3\")) (dir-of /tmp))))"
                          n (string-append dir "/in") n n))
    (let ([r (run-capturing 'broken)])
      (assert (and (car r) (contains? (car r) "<string>:5:26: step failed (exit 3)")))
      (assert (string=? (cdr r) "")))
    (putenv "DISEGNO_LOGS" "1")
    ;; The report: one line per item, with the program's names; prepare does not see the input and is
    ;; environment; live-direct fails, and the step's last lines say why.
    (let* ([r (run-capturing 'live-direct)] [msg (car r)] [out (cdr r)])
      (assert (> streamed 0))                                 ; the lines came from the stream
      (assert (contains? out "✓ sets up the environment  "))
      (assert (contains? out "✗ live-direct  <string>:12:26  exit 3  "))
      (assert (contains? out (format "\n      evil~a\n" n)))
      (assert (not (contains? out (format "A~a" n))))         ; the proof of what went well is not printed
      (assert (and msg (contains? msg "<string>:12:26: step failed (exit 3)"))))
    ;; A failed Dockerfile RUN is not an item: its last lines come from the error.
    (check-string (format "(claim broken-context Dir)
(define broken-context (with-file empty /Dockerfile \"FROM busybox@sha256:bdf57e528e45e4433820e045b29b4597825a1c9e38353532d90a01445013f82e\\nRUN echo docker~a >&2 && exit 4\\n\"))
(claim broken-build (Export Dir))
(define broken-build (overlay \"broken\" (dir-of (build-dockerfile broken-context \"Dockerfile\" (list) (list)) /tmp)))" n))
    (let ([r (run-capturing 'broken-build)])
      (assert (contains? (cdr r) (format "│ docker~a\n" n)))
      (assert (and (car r) (contains? (car r) "step failed (exit 4)"))))
    ;; In CI the proof sits in the item's group: stdout and stderr interleaved. The first step is now
    ;; cached: the stream is silent, and the proof is combinedOutput.
    (set! logged '())                                         ; a new run, like a new process
    (putenv "GITHUB_ACTIONS" "true")
    (let ([out (cdr (run-capturing 'live-direct))])
      (putenv "GITHUB_ACTIONS" "")
      (assert (contains? out "::group::✓ sets up the environment  "))
      (assert (contains? out (format "\"\nA~a\nB\nC\n" n)))
      (assert (contains? out "::error file=<string>,line=12,col=26::step failed (exit 3)"))))
  ;; Outputs come in then's order, and the report shows the effect with its command.
  (let ([r2 (begin (set! logged '()) (run-capturing 'sequence))])
    (assert (contains? (cdr r2) "✓ sequence    sh -c \"echo effect\"  "))
    (assert (contains? (cdr r2) "realized in "))
    (assert (contains? (cdr r2) ": effect sh -c \"echo effect\", exported "))
    (assert (string=? (call-with-input-file (string-append dir "/out5/after") get-string-all) "yes\n")))
  ;; An item with a docstring is a single line even with two effects (two chains), and the last
  ;; line says the label, not the commands.
  (let ([n (time-nanosecond (current-time))])
    (check-string (format "(claim two-steps (Export Dir))
(define two-steps \"does two things\"
  (begin (apply (pipe (container) (from \"alpine\")) (list \"sh\" \"-c\" \"echo one~a\"))
         (apply (pipe (container) (from \"alpine\")) (list \"sh\" \"-c\" \"echo two~a\"))))" n n))
    (set! logged '())
    (let ([out (cdr (run-capturing 'two-steps))])
      (assert (= 1 (length (filter (lambda (l) (contains? l "does two things  ")) (last-lines out 50)))))
      (assert (contains? out ": does two things\n"))))
  (run 'secret-test)
  (assert (string=? (call-with-input-file (string-append dir "/out6/outcome") get-string-all) "received\n"))
  (run 'cli-aws)
  (assert (string=? (call-with-input-file (string-append dir "/out7/outcome") get-string-all) "answers\n"))
  (let ([r (run-capturing 'with-fallback)])                       ; it fails, but the fallback first
    (assert (and (car r) (contains? (car r) "step failed (exit 3)")))
    (assert (file-exists? (string-append dir "/out13/before")))
    (assert (file-exists? (string-append dir "/out13/fallback"))))
  (for-each (lambda (e f t) (run e) (assert (string=? (call-with-input-file (string-append dir "/out14/" f) get-string-all) t)))
            '(with-registry with-gitops with-argocd) '("registry" "gitops" "argocd") '("pushed\n" "updated\n" "answers\n"))
  (run 'with-dockerfile)
  (assert (string=? (call-with-input-file (string-append dir "/out15/outcome") get-string-all) "read 1.2\n"))
  (run 'filters)
  (assert (zero? (system (format "test -x ~a/out9/run.sh" dir))))
  (assert (not (file-exists? (string-append dir "/out9/note.txt"))))
  (when (getenv "DISEGNO_TEST_KEY")
    (run 'with-secrets)
    (assert (string=? (call-with-input-file (string-append dir "/out11/outcome") get-string-all) "received\n"))
    (run 'with-s3)
    (assert (string=? (call-with-input-file (string-append dir "/out10/outcome") get-string-all) "published\n"))
    (run 'with-localstack)
    (assert (string=? (call-with-input-file (string-append dir "/out8/outcome") get-string-all) "scritto\n")))
  (system (format "rm -rf ~a" dir))
  (display "live: ok\n"))
(display "ok\n")
