;; Disegno's type checker.
;; Elaborator (untrusted): names, implicit arguments, metavariables, patterns.
;; Kernel (trusted): rechecks every elaborated term, with stratified universes.
;; elaboration-zoo style (Kovács): terms with de Bruijn indices, values with levels, NbE.
;;
;; Terms:  (var i) (glob n) (app f u i) (lam x i b) (pi x i a b) (type n) (meta m) (imeta m) (str s)
;; Values: (vlam x i env b) (vpi x i a env b) (vtype n) (vrigid l sp) (vflex m sp) (vglob n sp) (vstr s)
;; Visibility i ∈ {e, i}. Spine: a list of (value . visibility) in application order.

(define here (make-parameter #f))                        ; the position nearest to what is being elaborated
(define (oops fmt . args)
  (let ([msg (apply format fmt args)])
    (error (quote disegno) (if (here) (string-append (pos->string (here)) ": " msg) msg))))

;; --- globals and metavariables ---

;; data: constructors; con: data; def: (arity . clauses); extern: (GraphQL field . argument names)
(define-record-type g (fields kind type (mutable info)))
(define sigs (make-eq-hashtable))                       ; def → elaborated signature, not reduced (for the runner)
(define privileged (make-parameter #f))                 ; extern only in the standard library
(define globals (make-eq-hashtable))
(define (gget n) (and (symbol? n) (hashtable-ref globals n #f)))
(define def-pos (make-eq-hashtable))                    ; global → position of its definition (for the LSP)
(define (define-global! n g) (hashtable-set! globals n g) (when (here) (hashtable-set! def-pos n (here))))

;; Builtin: the library names the core knows. The keys are a closed list of the core; the
;; library binds each key to one of its names with (builtin key name), like Agda's BUILTIN.
;; So the checker does not name the library: the literals 0, "x", /out, [a b] and
;; "10.0.0.0/8", the proofs computed by auto, acceleration and the plan go through here.
;; Trusted like extern: only the kind of the name is checked, not that it has the expected shape.
(define builtin-keys                                    ; key → kind of the name
  '((nat . data) (zero . con) (suc . con)                ; the numerals 0, 1, 2…
    (bool . data) (true . con) (false . con)             ; the results of primitives and acceleration
    (unit . data) (tt . con) (empty . data) (eq . data) (refl . con) (sigma . data)   ; auto
    (list . data) (nil . con) (cons . con)               ; [a b]
    (string . extern)                                    ; "…"
    (abs . data) (root . con) (slash . con) (rel . data) (here . con) (step . con) (segment . data)   ; /out, "bin/x"
    (duration . data) (instant . data) (ip . data) (cidr . data)   ; literals read by type
    (plus . def) (monus . def) (times . def) (leq? . def) (lt? . def) (nat-eq? . def) (pow2 . def)   ; accelerated
    (obj . data) (host . def) (host-secret . def) (host-env . def) (host-choice . def)))   ; the plan, and main's inputs
(define builtins (make-eq-hashtable))                   ; key → name
(define builtin-of (make-eq-hashtable))                 ; name → key
(define (bi k) (hashtable-ref builtins k #f))
(define (bi? n k) (and n (eq? n (hashtable-ref builtins k #f))))

(define (check-builtin d)
  (unless (privileged) (oops "builtin is reserved to the standard library"))
  (unless (and (= (length d) 3) (symbol? (cadr d)) (symbol? (caddr d))) (oops "malformed builtin: ~s" d))
  (let* ([k (cadr d)] [n (caddr d)] [kind (assq k builtin-keys)] [g (gget n)])
    (unless kind (oops "builtin: unknown key ~a" k))
    (when (bi k) (oops "builtin: ~a is already bound to ~a" k (bi k)))
    (unless (and g (eq? (g-kind g) (cdr kind))) (oops "builtin ~a: ~a is not a ~a" k n (cdr kind)))
    (hashtable-set! builtins k n)
    (hashtable-set! builtin-of n k)))
(define (con? n) (let ([g (gget n)]) (and g (eq? (g-kind g) 'con))))
(define (fresh-name! n)
  (when (memq n '(→ Type _ TODO pipe auto let λ the)) (oops "~a is a reserved word" n))
  (when (gget n) (oops "~a is already defined" n)))

(define metas (make-eqv-hashtable))                     ; m → #(solution name type)
(define (new-meta name type)
  (let ([m (+ 1 (hashtable-size metas))]) (hashtable-set! metas m (vector #f name type)) m))
(define (meta-sol m) (vector-ref (hashtable-ref metas m #f) 0))
(define (meta-name m) (vector-ref (hashtable-ref metas m #f) 1))
(define (meta-type m) (vector-ref (hashtable-ref metas m #f) 2))
(define (solve! m v) (vector-set! (hashtable-ref metas m #f) 0 v))
(define (meta-val m) (or (meta-sol m) `(vflex ,m ())))

(define pmetas '())                                     ; pattern variables of the current clause
(define (new-pmeta name type) (let ([m (new-meta name type)]) (set! pmetas (cons m pmetas)) m))

;; --- evaluation ---

(define (vvar l) `(vrigid ,l ()))
(define (pi-dom v) (list-ref v 3))
(define (pi-cod v u) (ev (cons u (list-ref v 4)) (list-ref v 5)))

(define (ev env t)
  (case (car t)
    [(var) (list-ref env (cadr t))]
    [(glob) (reduce (cadr t) '())]
    [(app) (vapp (ev env (cadr t)) (ev env (caddr t)) (cadddr t))]
    [(lam) `(vlam ,(cadr t) ,(caddr t) ,env ,(cadddr t))]
    [(pi) `(vpi ,(cadr t) ,(caddr t) ,(ev env (cadddr t)) ,env ,(list-ref t 4))]
    [(type) `(vtype ,(cadr t))]
    [(str) `(vstr ,(cadr t))]
    [(num) `(vnum ,(cadr t))]
    [(ann) (ev env (cadr t))]                            ; (ann t T): the annotation does not compute
    [(at) (let ([v (ev env (caddr t))])                 ; a step remembers where it is in the source
            (if (and (pair? v) (eq? (car v) 'vglob)) (list 'vglob (cadr v) (caddr v) (cadr t) (current-item) (current-question)) v))]
    [(meta) (meta-val (cadr t))]
    [(imeta) (fold-left (lambda (f v) (vapp f v 'e)) (meta-val (cadr t)) (reverse env))]))

(define (vapp f u i)
  (let ([a (list (cons u i))])
    (case (car f)
      [(vlam) (ev (cons u (cadddr f)) (list-ref f 4))]
      [(vflex vrigid) `(,(car f) ,(cadr f) ,(append (caddr f) a))]
      [(vglob) (in-item-of f (lambda () (reduce (cadr f) (append (caddr f) a))))]
      [else (ufail 'mismatch)])))
(define (vapp-sp f sp) (fold-left (lambda (f a) (vapp f (car a) (cdr a))) f sp))

(define (force v)
  (case (car v)
    [(vflex) (let ([s (meta-sol (cadr v))]) (if s (force (vapp-sp s (caddr v))) v))]
    [(vglob) (let ([r (in-item-of v (lambda () (try-reduce (cadr v) (caddr v))))]) (if r (force r) (numeral v)))]
    [else v]))

;; Native numerals: in the logic Nat is zero/add1, in the evaluator a number is a Scheme integer
;; (as in Lean). zero and add1 of a number become numbers; an add1 pattern subtracts 1.
(define (numeral v)
  (let ([sp (caddr v)])
    (cond [(and (bi? (cadr v) 'zero) (null? sp)) '(vnum 0)]
          [(and (bi? (cadr v) 'suc) (= (length sp) 1))
           (let ([x (force (caar sp))]) (if (eq? (car x) 'vnum) `(vnum ,(+ 1 (cadr x))) v))]
          [else v])))

;; A def reduces when it has all its arguments and a clause matches; otherwise it stays stuck.
;; A stuck value (on an input the runner resolves later, like Host-env) remembers the item it was
;; born in: once unstuck, its steps still belong to that item.
(define (reduce n sp)
  (or (try-reduce n sp) (if (or (current-item) (current-question)) `(vglob ,n ,sp #f ,(current-item) ,(current-question)) `(vglob ,n ,sp))))
(define (in-item-of v thunk)
  (if (> (length v) 4) (parameterize ([current-item (or (list-ref v 4) (current-item))] [current-question (or (v-question v) (current-question))]) (thunk)) (thunk)))
(define (try-reduce n sp)
  (let* ([g (gget n)] [info (and (eq? (g-kind g) 'def) (g-info g))])
    (cond [(and info (accelerate) (let ([f (assq (hashtable-ref builtin-of n #f) fast)]) (and f (fast-apply f sp))))]   ; first: native numbers
          [info (and (>= (length sp) (car info))
                     (let ([r (if (hashtable-ref plan-items n #f)     ; an item's body: its steps
                                  (if (question? n)               ; a question: its steps belong to the item that asks it
                                      (parameterize ([current-question n]) (match-clauses (cdr info) (list-head sp (car info))))
                                      (parameterize ([current-item (enter-item n)]) (match-clauses (cdr info) (list-head sp (car info)))))
                                  (match-clauses (cdr info) (list-head sp (car info))))])
                       (and r (vapp-sp r (list-tail sp (car info))))))]
          [(and (eq? (g-kind g) 'extern) (assq (car (car (g-info g))) prims))
           => (lambda (p)                                ; pure primitive: computed on literals
                (let ([args (map (lambda (a) (force (car a))) sp)])
                  (and (= (length args) (cadr p)) (for-all (lambda (a) (memq (car a) '(vstr vnum))) args)
                       (let ([r (apply (caddr p) (map cadr args))])
                         (cond [(string? r) `(vstr ,r)] [(number? r) `(vnum ,r)]
                               [r `(vglob ,(bi 'true) ())] [else `(vglob ,(bi 'false) ())])))))]
          [else #f])))

;; Acceleration (trusted, as in Lean): these standard library defs, on numeric arguments, are
;; computed in Scheme instead of by clauses. In the logic the unary definitions stay; test.ss
;; checks that the two computations agree. accelerate is switched off for that comparison.
(define accelerate (make-parameter #t))
(define fast `((plus 2 ,+) (monus 2 ,(lambda (a b) (max 0 (- a b)))) (times 2 ,*)          ; by builtin key
               (leq? 2 ,<=) (lt? 2 ,<) (nat-eq? 2 ,=) (pow2 1 ,(lambda (k) (expt 2 k)))))
(define (fast-apply f sp)
  (and (= (length sp) (cadr f))
       (let ([args (map (lambda (a) (force (car a))) sp)])
         (and (for-all (lambda (a) (eq? (car a) 'vnum)) args)
              (let ([r (apply (caddr f) (map cadr args))])
                (cond [(number? r) `(vnum ,r)] [r `(vglob ,(bi 'true) ())] [else `(vglob ,(bi 'false) ())]))))))

;; Pure primitives (a closed list of the core): name → (arity procedure). They compute on literals
;; only, strings and numbers, and return a string, a number or a boolean.
(define (string-contains? s sub)
  (let ([n (string-length s)] [k (string-length sub)])
    (let loop ([i 0]) (and (<= (+ i k) n) (or (string=? (substring s i (+ i k)) sub) (loop (+ i 1)))))))
(define (split-on s ch)
  (let loop ([cs (string->list s)] [cur '()] [acc '()])
    (cond [(null? cs) (reverse (cons (list->string (reverse cur)) acc))]
          [(char=? (car cs) ch) (loop (cdr cs) '() (cons (list->string (reverse cur)) acc))]
          [else (loop (cdr cs) (cons (car cs) cur) acc)])))

;; Image reference: [registry/]name[/name…][:tag][@sha256:<64 hex digits>]
;; ponytail: a simplified distribution/reference grammar; no digests other than sha256.
(define (image-ref? s)
  (define (low? c) (or (char-numeric? c) (and (char-alphabetic? c) (char-lower-case? c))))
  (define (chars-ok? x ok?) (for-all ok? (string->list x)))
  (define (component? x)
    (let ([n (string-length x)])
      (and (> n 0) (low? (string-ref x 0)) (low? (string-ref x (- n 1)))
           (chars-ok? x (lambda (c) (or (low? c) (memv c '(#\. #\_ #\-))))))))
  (define (registry? x)
    (and (or (memv #\. (string->list x)) (memv #\: (string->list x)) (string=? x "localhost"))
         (chars-ok? x (lambda (c) (or (char-alphabetic? c) (char-numeric? c) (memv c '(#\. #\- #\:)))))))
  (define (tag? x)
    (and (<= 1 (string-length x) 128) (not (memv (string-ref x 0) '(#\. #\-)))
         (chars-ok? x (lambda (c) (or (char-alphabetic? c) (char-numeric? c) (memv c '(#\_ #\. #\-)))))))
  (define (digest? x)
    (and (= (string-length x) 71) (string=? (substring x 0 7) "sha256:")
         (chars-ok? (substring x 7 71) (lambda (c) (or (char-numeric? c) (memv c (string->list "abcdef")))))))
  (let ([at (split-on s #\@)])
    (and (<= 1 (length at) 2) (or (null? (cdr at)) (digest? (cadr at)))
         (let* ([parts (split-on (car at) #\/)]
                [name+tag (split-on (list-ref parts (- (length parts) 1)) #\:)]
                [path (list-head parts (- (length parts) 1))])
           (and (<= 1 (length name+tag) 2) (or (null? (cdr name+tag)) (tag? (cadr name+tag)))
                (component? (car name+tag))
                (for-all component? (if (and (pair? path) (registry? (car path))) (cdr path) path)))))))

;; Literal readers (core): string → the value's fields, or #f if malformed. The constructor is the
;; only one of the type bound to the key (builtin duration Duration…); proofs are computed by auto.
(define (digits->nat s)
  (and (> (string-length s) 0) (for-all char-numeric? (string->list s)) (string->number s)))

(define (read-duration s)                                ; "90s", "5m", "1h30m", "2d" → (seconds)
  (let loop ([cs (string->list s)] [num '()] [total 0] [any #f])
    (cond [(null? cs) (and any (null? num) (list total))]
          [(char-numeric? (car cs)) (loop (cdr cs) (cons (car cs) num) total any)]
          [(and (pair? num) (assv (car cs) '((#\d . 86400) (#\h . 3600) (#\m . 60) (#\s . 1))))
           => (lambda (u) (loop (cdr cs) '() (+ total (* (cdr u) (string->number (list->string (reverse num))))) #t))]
          [else #f])))

(define (days-from-civil y m d)                          ; H. Hinnant: days since 1970-01-01
  (let* ([y (if (<= m 2) (- y 1) y)] [era (floor (/ y 400))] [yoe (- y (* era 400))]
         [doy (+ (quotient (+ (* 153 (+ m (if (> m 2) -3 9))) 2) 5) (- d 1))]
         [doe (+ (* yoe 365) (quotient yoe 4) (- (quotient yoe 100)) doy)])
    (+ (* era 146097) doe -719468)))

(define (read-instant s)                                 ; "2026-10-15" or "2026-10-15T10:00:00Z" → (seconds)
  (let ([n (string-length s)])
    (and (or (= n 10) (and (= n 20) (char=? (string-ref s 10) #\T) (char=? (string-ref s 19) #\Z)
                           (char=? (string-ref s 13) #\:) (char=? (string-ref s 16) #\:)))
         (char=? (string-ref s 4) #\-) (char=? (string-ref s 7) #\-)
         (let ([y (digits->nat (substring s 0 4))] [mo (digits->nat (substring s 5 7))] [d (digits->nat (substring s 8 10))]
               [h (if (= n 20) (digits->nat (substring s 11 13)) 0)] [mi (if (= n 20) (digits->nat (substring s 14 16)) 0)]
               [se (if (= n 20) (digits->nat (substring s 17 19)) 0)])
           (and y mo d h mi se (<= 1 mo 12) (<= 1 d 31) (< h 24) (< mi 60) (< se 60) (>= y 1970)
                (list (+ (* 86400 (days-from-civil y mo d)) (* 3600 h) (* 60 mi) se)))))))

(define (ip->nat s)                                      ; "10.0.0.5" → 167772165
  (let ([parts (split-on s #\.)])
    (and (= (length parts) 4)
         (let ([os (map digits->nat parts)])
           (and (for-all (lambda (o) (and o (<= o 255))) os)
                (fold-left (lambda (acc o) (+ (* acc 256) o)) 0 os))))))

(define (read-ip s) (let ([n (ip->nat s)]) (and n (list n))))

(define (read-cidr s)                                    ; "10.0.0.0/8": the block is (prefix, length)
  (let ([parts (split-on s #\/)])
    (and (= (length parts) 2)
         (let ([base (ip->nat (car parts))] [len (digits->nat (cadr parts))])
           (and base len (<= len 32)
                (let ([size (expt 2 (- 32 len))])
                  (and (= 0 (remainder base size)) (list (quotient base size) len))))))))

(define readers `((duration . ,read-duration) (instant . ,read-instant) (ip . ,read-ip) (cidr . ,read-cidr)))

;; A path step: not empty, no /, neither . nor ..
(define (segment? s) (and (> (string-length s) 0) (not (memv #\/ (string->list s))) (not (member s '("." "..")))))

(define (nat->ip n)                                      ; 167772165 → "10.0.0.5"
  (format "~a.~a.~a.~a" (quotient n 16777216) (remainder (quotient n 65536) 256) (remainder (quotient n 256) 256) (remainder n 256)))

;; Regular expressions (pure primitive, on literals): the match is against the whole string.
;; Syntax: characters, . [a-z] [^…] \d \w \s \x, groups ( ), alternatives |, * + ? {n} {n,} {n,m}.
;; A repetition goes on only if it consumes, so matching terminates even on (a*)*.
;; ponytail: backtracking, exponential in pathological cases; patterns on names and ARNs suffice.
(define (re-parse pat)                                   ; → tree, or a type error if malformed
  (define cs (list->vector (string->list pat)))
  (define n (vector-length cs))
  (define i 0)
  (define (bad) (oops "re?: malformed regular expression: ~s" pat))
  (define (peek) (and (< i n) (vector-ref cs i)))
  (define (next!) (let ([c (peek)]) (unless c (bad)) (set! i (+ i 1)) c))
  (define (esc c)                                        ; \d \w \s, or the character itself
    (case c
      [(#\d) '(cls #f ((#\0 . #\9)))]
      [(#\w) '(cls #f ((#\a . #\z) (#\A . #\Z) (#\0 . #\9) (#\_ . #\_)))]
      [(#\s) '(cls #f ((#\space . #\space) (#\tab . #\tab) (#\newline . #\newline) (#\return . #\return)))]
      [else `(chr ,c)]))
  (define (number)
    (let loop ([v #f]) (let ([c (peek)]) (if (and c (char-numeric? c)) (begin (next!) (loop (+ (* 10 (or v 0)) (- (char->integer c) 48)))) v))))
  (define (klass)                                        ; after [
    (let ([neg (and (eqv? (peek) #\^) (next!) #t)])
      (let loop ([rs '()])
        (let ([c (next!)])
          (cond [(and (char=? c #\]) (pair? rs)) `(cls ,neg ,(reverse rs))]
                [(char=? c #\\) (let ([e (esc (next!))]) (loop (if (eq? (car e) 'cls) (append (reverse (caddr e)) rs) (cons (cons (cadr e) (cadr e)) rs))))]
                [(and (eqv? (peek) #\-) (< (+ i 1) n) (not (char=? (vector-ref cs (+ i 1)) #\])))
                 (next!) (let ([hi (next!)]) (when (char<? hi c) (bad)) (loop (cons (cons c hi) rs)))]
                [else (loop (cons (cons c c) rs))])))))
  (define (atom)
    (let ([c (next!)])
      (case c
        [(#\() (let ([r (alt)]) (unless (eqv? (next!) #\)) (bad)) r)]
        [(#\[) (klass)]
        [(#\.) '(any)]
        [(#\\) (esc (next!))]
        [(#\* #\+ #\? #\{ #\)) (bad)]
        [else `(chr ,c)])))
  (define (quant r)
    (case (peek)
      [(#\*) (next!) (quant `(rep ,r 0 #f))]
      [(#\+) (next!) (quant `(rep ,r 1 #f))]
      [(#\?) (next!) (quant `(rep ,r 0 1))]
      [(#\{) (next!)
       (let* ([lo (or (number) (bad))]
              [hi (if (eqv? (peek) #\,) (begin (next!) (number)) lo)])
         (unless (eqv? (next!) #\}) (bad))
         (when (and hi (< hi lo)) (bad))
         (quant `(rep ,r ,lo ,hi)))]
      [else r]))
  (define (seq)
    (let loop ([acc '()])
      (if (memv (peek) '(#f #\| #\)))
          `(seq ,@(reverse acc))
          (loop (cons (quant (atom)) acc)))))
  (define (alt)
    (let ([l (seq)]) (if (eqv? (peek) #\|) (begin (next!) `(alt ,l ,(alt))) l)))
  (let ([r (alt)]) (when (< i n) (bad)) r))

(define (re-match? r s)
  (define n (string-length s))
  (define (m r i k)                                      ; k: the continuation, from the index reached
    (case (car r)
      [(chr) (and (< i n) (char=? (string-ref s i) (cadr r)) (k (+ i 1)))]
      [(any) (and (< i n) (k (+ i 1)))]
      [(cls) (and (< i n)
                  (let* ([c (string-ref s i)] [in (exists (lambda (p) (char<=? (car p) c (cdr p))) (caddr r))])
                    (and (if (cadr r) (not in) in) (k (+ i 1)))))]
      [(seq) (let loop ([rs (cdr r)] [i i]) (if (null? rs) (k i) (m (car rs) i (lambda (j) (loop (cdr rs) j)))))]
      [(alt) (or (m (cadr r) i k) (m (caddr r) i k))]
      [(rep) (let ([x (cadr r)] [lo (caddr r)] [hi (cadddr r)])
               (let loop ([count 0] [i i])               ; greedy: one more repetition first
                 (or (and (or (not hi) (< count hi))
                          (m x i (lambda (j) (and (or (> j i) (< count lo)) (loop (+ count 1) j)))))
                     (and (>= count lo) (k i)))))]))
  (m r 0 (lambda (j) (= j n))))

(define re-cache (make-hashtable string-hash string=?))
(define (re? pat s)
  (re-match? (or (hashtable-ref re-cache pat #f) (let ([r (re-parse pat)]) (hashtable-set! re-cache pat r) r)) s))

(define prims `((%concat 2 ,string-append) (%show 1 ,number->string) (%show-ip 1 ,nat->ip)
                (%contains? 2 ,string-contains?) (%distinct? 2 ,(lambda (a b) (not (string=? a b))))
                (%re? 2 ,re?)
                (%image-ref? 1 ,image-ref?) (%segment? 1 ,segment?)))

;; A run-time clause: (patterns n body); pattern: (pvar level) (pdot) (pcon c pattern...).
(define (match-clauses cs args)
  (and (pair? cs)
       (let* ([c (car cs)] [env (make-vector (cadr c) #f)])
         (case (match-all (car c) (map car args) env)
           [(yes) (ev (reverse (vector->list env)) (caddr c))]
           [(no) (match-clauses (cdr cs) args)]
           [else #f]))))
(define (match-all ps vs env)
  (if (null? ps) 'yes
      (let ([r (match (car ps) (car vs) env)])
        (if (eq? r 'yes) (match-all (cdr ps) (cdr vs) env) r))))
(define (match p v env)
  (case (car p)
    [(pvar) (vector-set! env (cadr p) v) 'yes]
    [(pdot) 'yes]
    [(pcon) (let ([v (force v)])
              (cond [(eq? (car v) 'vnum)
                     (cond [(and (bi? (cadr p) 'zero) (= (cadr v) 0)) 'yes]
                           [(and (bi? (cadr p) 'suc) (> (cadr v) 0)) (match (car (caddr p)) `(vnum ,(- (cadr v) 1)) env)]
                           [else 'no])]
                    [(not (and (eq? (car v) 'vglob) (con? (cadr v)))) 'stuck]
                    [(eq? (cadr v) (cadr p)) (match-all (caddr p) (map car (caddr v)) env)]
                    [else 'no]))]))

(define (reify l v)
  (let ([v (force v)])
    (define (sp h) (fold-left (lambda (t a) `(app ,t ,(reify l (car a)) ,(cdr a))) h (caddr v)))
    (case (car v)
      [(vflex) (sp `(meta ,(cadr v)))]
      [(vrigid) (sp `(var ,(- l (cadr v) 1)))]
      [(vglob) (sp `(glob ,(cadr v)))]
      [(vlam) `(lam ,(cadr v) ,(caddr v) ,(reify (+ l 1) (vapp v (vvar l) (caddr v))))]
      [(vpi) `(pi ,(cadr v) ,(caddr v) ,(reify l (pi-dom v)) ,(reify (+ l 1) (pi-cod v (vvar l))))]
      [(vtype) `(type ,(cadr v))]
      [(vstr) `(str ,(cadr v))]
      [(vnum) `(num ,(cadr v))])))

;; --- unification (without metavariables it is the kernel's conversion) ---

(define-record-type unify-failure (fields kind))         ; conflict | mismatch | stuck | occurs | scope
(define (ufail k) (raise (make-unify-failure k)))

(define (unify l a b)
  (let ([a (force a)] [b (force b)])
    (define (is? v tag) (eq? (car v) tag))
    (cond
      [(or (is? a 'vlam) (is? b 'vlam))
       (let ([i (caddr (if (is? a 'vlam) a b))])
         (unify (+ l 1) (vapp a (vvar l) i) (vapp b (vvar l) i)))]
      [(and (is? a 'vpi) (is? b 'vpi) (eq? (caddr a) (caddr b)))
       (unify l (pi-dom a) (pi-dom b))
       (unify (+ l 1) (pi-cod a (vvar l)) (pi-cod b (vvar l)))]
      [(and (is? a 'vtype) (is? b 'vtype) (= (cadr a) (cadr b))) (void)]
      [(and (is? a 'vstr) (is? b 'vstr)) (unless (string=? (cadr a) (cadr b)) (ufail 'conflict))]
      [(and (is? a 'vrigid) (is? b 'vrigid) (= (cadr a) (cadr b))) (unify-sp l (caddr a) (caddr b))]
      [(and (is? a 'vglob) (is? b 'vglob))
       (cond [(eq? (cadr a) (cadr b)) (unify-sp l (caddr a) (caddr b))]
             [(and (con? (cadr a)) (con? (cadr b))) (ufail 'conflict)]
             [else (ufail 'mismatch)])]
      [(and (is? a 'vflex) (is? b 'vflex) (= (cadr a) (cadr b))) (unify-sp l (caddr a) (caddr b))]
      ;; flex-flex: solve the meta with the larger context, so the other stays in its scope
      [(and (is? a 'vflex) (is? b 'vflex) (< (length (caddr a)) (length (caddr b)))) (solve l (cadr b) (caddr b) a)]
      [(is? a 'vflex) (solve l (cadr a) (caddr a) b)]
      [(is? b 'vflex) (solve l (cadr b) (caddr b) a)]
      [(and (is? a 'vnum) (is? b 'vnum)) (unless (= (cadr a) (cadr b)) (ufail 'conflict))]
      [(is? a 'vnum) (unify-num l (cadr a) b)]
      [(is? b 'vnum) (unify-num l (cadr b) a)]
      [else (ufail 'mismatch)])))

(define (unify-num l n b)                               ; a number against add1 x, zero or else
  (cond [(and (eq? (car b) 'vglob) (bi? (cadr b) 'suc) (= (length (caddr b)) 1))
         (if (= n 0) (ufail 'conflict) (unify l `(vnum ,(- n 1)) (caar (caddr b))))]
        [(and (eq? (car b) 'vglob) (con? (cadr b))) (ufail 'conflict)]
        [else (ufail 'mismatch)]))

(define (unify-sp l s1 s2)
  (unless (= (length s1) (length s2)) (ufail 'mismatch))
  (for-each (lambda (x y) (unify l (car x) (car y))) s1 s2))

;; Miller pattern unification: ?m x1..xn = rhs, with xi distinct variables.
(define (solve l m sp rhs)
  (let ([t (rename-v m (length sp) l (invert sp) rhs)])
    (solve! m (ev '() (fold-right (lambda (a t) `(lam x ,(cdr a) ,t)) t sp)))))

(define (invert sp)                                     ; level in the context → level in the solution
  (let loop ([sp sp] [k 0] [ren '()])
    (if (null? sp) ren
        (let ([v (force (caar sp))])
          (unless (and (eq? (car v) 'vrigid) (null? (caddr v)) (not (assv (cadr v) ren))) (ufail 'stuck))
          (loop (cdr sp) (+ k 1) (cons (cons (cadr v) k) ren))))))

(define (rename-v m dom cod ren v)
  (let ([v (force v)])
    (define (sp h) (fold-left (lambda (t a) `(app ,t ,(rename-v m dom cod ren (car a)) ,(cdr a))) h (caddr v)))
    (define (under f) (rename-v m (+ dom 1) (+ cod 1) (cons (cons cod dom) ren) (f (vvar cod))))
    (case (car v)
      [(vflex) (if (= (cadr v) m) (ufail 'occurs) (sp `(meta ,(cadr v))))]
      [(vrigid) (let ([p (assv (cadr v) ren)])
                  (if p (sp `(var ,(- dom (cdr p) 1))) (ufail 'scope)))]
      [(vglob) (sp `(glob ,(cadr v)))]
      [(vlam) `(lam ,(cadr v) ,(caddr v) ,(under (lambda (x) (vapp v x (caddr v)))))]
      [(vpi) `(pi ,(cadr v) ,(caddr v) ,(rename-v m dom cod ren (pi-dom v)) ,(under (lambda (x) (pi-cod v x))))]
      [(vtype) `(type ,(cadr v))]
      [(vstr) `(str ,(cadr v))]
      [(vnum) `(num ,(cadr v))])))

;; --- kernel: the only trusted part of checking ---

(define (k-infer env tys l t)
  (case (car t)
    [(var) (list-ref tys (cadr t))]
    [(glob) (let ([g (gget (cadr t))]) (if g (g-type g) (oops "kernel: ~a does not exist" (cadr t))))]
    [(type) `(vtype ,(+ (cadr t) 1))]                   ; Type n : Type n+1, never Type : Type
    [(str) (string-type)]
    [(num) `(vglob ,(bi 'nat) ())]
    [(ann) (let ([ty (ev env (caddr t))]) (k-type-in env tys l (caddr t)) (k-check env tys l (cadr t) ty) ty)]
    [(at) (k-infer env tys l (caddr t))]
    [(pi) (let ([la (k-level (k-infer env tys l (cadddr t)))])
            `(vtype ,(max la (k-level (k-infer (cons (vvar l) env) (cons (ev env (cadddr t)) tys) (+ l 1) (list-ref t 4))))))]
    [(app) (let ([tf (force (k-infer env tys l (cadr t)))])
             (unless (and (eq? (car tf) 'vpi) (eq? (caddr tf) (cadddr t))) (oops "kernel: ill-typed application"))
             (k-check env tys l (caddr t) (pi-dom tf))
             (pi-cod tf (ev env (caddr t))))]
    [else (oops "kernel: term not inferable ~s" t)]))

(define (k-check env tys l t ty)
  (let ([ty (force ty)])
    (if (and (eq? (car t) 'lam) (eq? (car ty) 'vpi) (eq? (caddr t) (caddr ty)))
        (k-check (cons (vvar l) env) (cons (pi-dom ty) tys) (+ l 1) (cadddr t) (pi-cod ty (vvar l)))
        (guard (x [(unify-failure? x) (oops "kernel: wrong type")])
          (unify l (k-infer env tys l t) ty)))))

(define (k-level ty)
  (let ([ty (force ty)]) (if (eq? (car ty) 'vtype) (cadr ty) (oops "kernel: expected a type"))))
(define (k-type t) (k-level (k-infer '() '() 0 t)))
(define (k-type-in env tys l t) (k-level (k-infer env tys l t)))

;; --- elaborator ---

(define-record-type ctx (fields l env tys names defs))  ; defs: forced pattern variables, (name value type)
(define ctx0 (make-ctx 0 '() '() '() '()))
(define (bind c x ty)
  (make-ctx (+ 1 (ctx-l c)) (cons (vvar (ctx-l c)) (ctx-env c)) (cons ty (ctx-tys c)) (cons x (ctx-names c)) (ctx-defs c)))
(define (define-name c x v ty)
  (make-ctx (ctx-l c) (ctx-env c) (ctx-tys c) (ctx-names c) (cons (list x v ty) (ctx-defs c))))

(define (index-of x xs)
  (let loop ([xs xs] [i 0]) (cond [(null? xs) #f] [(equal? (car xs) x) i] [else (loop (cdr xs) (+ i 1))])))
(define (nat? e) (and (integer? e) (exact? e) (>= e 0)))
(define (nat n) (if (zero? n) `(glob ,(bi 'zero)) `(app (glob ,(bi 'suc)) ,(nat (- n 1)) e)))
(define (string-type) (if (bi 'string) `(vglob ,(bi 'string) ()) (oops "string literals need String: (import text)")))

;; [..] arrives as (%br ..) (see brackets): in (→ ...) it is a binder [x T], in a term a list.
(define (binder? e) (and (pair? e) (memq (car e) '(%br %imp)) (= (length e) 3) (symbol? (cadr e))))  ; %imp: implicit, internal only
(define (unbracket e) (if (and (pair? e) (eq? (car e) '%br)) (cdr e) e))

(define (infer c e)                                     ; → (values term type)
  (with-pos e (lambda () (log-scope! c) (let-values ([(t ty) (infer* c e)]) (values (at-step e t) ty)))))
(define (infer* c e)
  (cond
    [(eq? e 'Type) (values '(type 0) '(vtype 1))]
    [(string? e) (values `(str ,e) (string-type))]
    [(eq? e '_) (oops "_ is not a term")]
    [(eq? e 'TODO) (oops "TODO: the type is not known here; annotate it with (the T TODO)")]
    [(nat? e) (unless (bi 'nat) (oops "numeric literals need the nat builtin")) (values `(num ,e) `(vglob ,(bi 'nat) ()))]
    [(symbol? e)
     (cond [(index-of e (ctx-names c)) => (lambda (i) (values `(var ,i) (list-ref (ctx-tys c) i)))]
           [(assq e (ctx-defs c)) => (lambda (d) (values (reify (ctx-l c) (cadr d)) (caddr d)))]
           [(and (not (privileged)) (char=? (string-ref (symbol->string e) 0) #\%)) (oops "~a is reserved to the core" e)]
           [(gget e) => (lambda (g) (values `(glob ,e) (g-type g)))]
           [(root-field e) => (lambda (n) (values `(glob ,n) (g-type (gget n))))]
           [(path-literal? e) (values (path-term c e) `(vglob ,(bi 'abs) ()))]
           [else (unknown-name e)])]
    [(let-form? e) (let-values ([(c body) (let-bind c e)]) (infer c body))]
    [(head? e '%match) (oops "match needs an expected type: write (the T (match …))")]
    [(and (pair? e) (eq? (car e) 'the) (= (length e) 3))   ; (the T e): e checked against T
     (let-values ([(ta n) (check-type c (cadr e))])
       (let ([ty (ev (ctx-env c) ta)]) (values `(ann ,(check c (caddr e) ty) ,ta) ty)))]
    [(lambda-form? e) (oops "λ needs an expected type: write (the T (λ …))")]
    [(and (pair? e) (eq? (car e) '→))
     (let-values ([(t n) (elab-arrow c (cdr e))]) (values t `(vtype ,n)))]
    [(and (pair? e) (eq? (car e) 'Type) (nat? (cadr e))) (values `(type ,(cadr e)) `(vtype ,(+ 1 (cadr e))))]
    [(and (pair? e) (eq? (car e) 'pipe) (pair? (cdr e))) ; (pipe x (f a) g) = (g (f x a))
     (infer c (fold-left (lambda (acc s)
                           (if (and (pair? s) (not (eq? (car s) '%br)))
                               (let ([n `(,(car s) ,acc ,@(cdr s))])   ; the step keeps its position
                                 (cond [(hashtable-ref pos-of s #f) => (lambda (p) (hashtable-set! pos-of n p))])
                                 n)
                               (list s acc)))
                         (cadr e) (cddr e)))]
    [(and (pair? e) (eq? (car e) '%br))                ; ["a" "b"] = (cons "a" (cons "b" nil))
     (infer c (fold-right (lambda (x acc) (list (bi 'cons) x acc)) (bi 'nil) (cdr e)))]
    [(and (pair? e) (symbol? (car e)) (not (known? c (car e))) (pair? (cdr e)) (pair? (qualified (car e))))
     ;; a short name with arguments: the type of the first argument picks the method (with-exec on
     ;; a Container is Container.with-exec); otherwise it is a root field. The first argument is
     ;; elaborated once only: inside pipe the chains are nested.
     (let*-values ([(t1 ty1) (infer c (cadr e))] [(t1 ty1) (insert c t1 ty1)])
       (let* ([self (reify (ctx-l c) ty1)]
              [n (or (find (lambda (n) (equal? (self-type n) self)) (qualified (car e)))
                     (root-field (car e))
                     (oops "~a does not exist for ~s" (car e) (show c ty1)))])
         (apply-args c e `(glob ,n) (g-type (gget n)) (cdr e) (cons t1 ty1))))]
    [(pair? e)
     (let-values ([(t ty) (infer c (car e))]) (apply-args c e t ty (cdr e) #f))]
    [else (oops "invalid expression: ~s" e)]))

;; pre: the first argument already elaborated, (term . type), or #f.
(define (apply-args c e t ty args pre)
  (if (null? args) (values t ty)
      (let-values ([(t ty) (insert c t ty)])
        (unless (and (eq? (car ty) 'vpi) (eq? (caddr ty) 'e)) (oops "too many arguments in ~s" e))
        (let ([u (if pre
                     (begin (guard (x [(unify-failure? x) (oops "~s: expected ~s, found ~s" (car args) (show c (pi-dom ty)) (show c (cdr pre)))])
                              (unify (ctx-l c) (cdr pre) (pi-dom ty)))
                            (car pre))
                     (check c (car args) (pi-dom ty)))])
          (apply-args c e `(app ,t ,u e) (pi-cod ty (ev (ctx-env c) u)) (cdr args) #f)))))

;; --- short names for the schema: Type.field is written field ---

(define (known? c e) (or (index-of e (ctx-names c)) (assq e (ctx-defs c)) (gget e)))

(define (qualified s)                                   ; the globals Type.s, in order
  (let* ([suffix (string-append "." (symbol->string s))] [k (string-length suffix)])
    (sort (lambda (a b) (string<? (symbol->string a) (symbol->string b)))
          (filter (lambda (n) (let ([str (symbol->string n)])
                                (and (> (string-length str) k) (string=? (substring str (- (string-length str) k) (string-length str)) suffix))))
                  (vector->list (hashtable-keys globals))))))

(define (root-field s)                                  ; a Query field is a top-level function
  (let ([n (string->symbol (format "Query.~a" s))]) (and (gget n) n)))

(define (self-type n)                                   ; type of the first explicit argument, reified
  (let loop ([t (force (g-type (gget n)))] [l 0])
    (and (eq? (car t) 'vpi)
         (if (eq? (caddr t) 'i) (loop (force (pi-cod t (vvar l))) (+ l 1)) (reify l (pi-dom t))))))

(define (insert c t ty)                                 ; applies the leading implicits with metavariables
  (let ([ty (force ty)])
    (if (and (eq? (car ty) 'vpi) (eq? (caddr ty) 'i))
        (let ([m `(imeta ,(new-meta #f #f))])
          (insert c `(app ,t ,m i) (pi-cod ty (ev (ctx-env c) m))))
        (values t ty))))

;; auto: proof by computation. Decidable propositions are written (So (test? ...)), which reduces
;; to ⊤ or ⊥; auto is tt when the expected type, computed, is ⊤, and refl when it is an equality.
;; For inductive relations, like (⊑ p q), it searches a proof by composing constructors.
(define (auto c ty)
  (let ([v (force ty)])
    (cond [(and (eq? (car v) 'vglob) (bi? (cadr v) 'unit)) `(glob ,(bi 'tt))]
          [(and (eq? (car v) 'vglob) (bi? (cadr v) 'eq)) (check c (bi 'refl) ty)]
          [(and (eq? (car v) 'vglob) (bi? (cadr v) 'empty)) (oops "auto: the proposition reduces to ⊥, not to true")]
          [(neg-dom v) => (lambda (a) (refutation c v a))]
          [else (let ([b (box #f)])
                  (or (parameterize ([blame b]) (search c v 32))
                      (if (unbox b)
                          (oops "auto: no proof of ~s" (show c (unbox b)))
                          (oops "auto: no proof of ~s" (show c ty)))))])))

;; Negations: (¬ A) is (→ A ⊥). auto searches the tree of absurd patterns covering A and has it
;; checked as an auxiliary definition: coverage and absurdity are checked by the checker.
(define (neg-dom v)
  (and (eq? (car v) 'vpi) (eq? (caddr v) 'e)
       (let ([cod (force (pi-cod v (vvar 0)))]) (and (eq? (car cod) 'vglob) (bi? (cadr cod) 'empty) (pi-dom v)))))

(define auto-count 0)
(define (refutation c v a)
  (unless (= (ctx-l c) 0) (oops "auto: refutation only on closed propositions"))
  (let ([pats (refute a 8)])
    (unless pats (oops "auto: no refutation of ~s" (show c a)))
    (set! auto-count (+ 1 auto-count))
    (let ([name (string->symbol (format "%auto~a" auto-count))])
      (check-def-core name (reify 0 v) (map (lambda (p) (cons (list p) #f)) pats))
      `(glob ,name))))

;; → patterns covering ty with absurdities, or #f. A constructor ruled out by the indices is not
;; needed; a possible one must be ruled out by one of its refutable fields.
(define (refute ty depth)
  (let ([v (force ty)])
    (and (> depth 0) (eq? (car v) 'vglob) (eq? (g-kind (gget (cadr v))) 'data)
         (not (has-meta? (reify 0 v)))
         (let loop ([ks (g-info (gget (cadr v)))] [acc '()])
           (if (null? ks)
               (if (null? acc) (list '()) acc)
               (let ([r (refute-con (car ks) v depth)])
                 (and r (loop (cdr ks) (if (eq? r 'impossible) acc (append acc r))))))))))

(define (refute-con k goal depth)
  (let loop ([kt (force (g-type (gget k)))] [fields '()])
    (if (eq? (car kt) 'vpi)
        (let ([m (meta-val (new-meta #f #f))])
          (loop (force (pi-cod kt m)) (if (eq? (caddr kt) 'e) (append fields (list (pi-dom kt))) fields)))
        (let ([r (guard (x [(unify-failure? x) (unify-failure-kind x)]) (unify 0 kt goal) 'ok)])
          (cond [(eq? r 'conflict) 'impossible]
                [(not (eq? r 'ok)) #f]
                [else (let try ([i 0] [fs fields])
                        (and (pair? fs)
                             (let ([ps (refute (car fs) (- depth 1))])
                               (if ps
                                   (map (lambda (p) (cons k (map (lambda (j) (if (= j i) p '_)) (iota (length fields))))) ps)
                                   (try (+ i 1) (cdr fs))))))])))))

(define (has-meta? z) (and (pair? z) (or (memq (car z) '(meta imeta)) (exists has-meta? z))))

;; ponytail: bounded depth-first search, first constructor that succeeds; enough for structural
;; relations like ⊑. Only on goals without metavariables, so failed attempts touch only new
;; metavariables.
;; blame: the first failed goal under a conjunction (×), to say which part does not hold.
(define blame (make-parameter #f))

(define (search c goal depth . conj)
  (let ([g (force goal)] [conj (or (null? conj) (car conj))])
    (and (> depth 0) (eq? (car g) 'vglob) (not (has-meta? (reify (ctx-l c) g)))
         (or (case (hashtable-ref builtin-of (cadr g) #f)
               [(unit) `(glob ,(bi 'tt))]
               [(eq) (guard (x [#t #f]) (check c (bi 'refl) g))]
               [else (let ([d (gget (cadr g))])
                       (and (eq? (g-kind d) 'data)
                            (exists (lambda (k) (try-constructor c k g depth conj)) (g-info d))))])
             (begin (when (and conj (blame) (not (unbox (blame))) (not (memq (hashtable-ref builtin-of (cadr g) #f) '(sigma unit empty))))
                      (set-box! (blame) g))
                    #f)))))

(define (try-constructor c k goal depth conj)
  (let loop ([t `(glob ,k)] [kt (g-type (gget k))] [holes '()])
    (let ([kt (force kt)])
      (if (eq? (car kt) 'vpi)
          (let* ([m `(imeta ,(new-meta #f #f))] [mv (ev (ctx-env c) m)])
            (loop `(app ,t ,m ,(caddr kt)) (pi-cod kt mv)
                  (if (eq? (caddr kt) 'e) (cons (cons mv (pi-dom kt)) holes) holes)))
          (and (guard (x [(unify-failure? x) #f]) (unify (ctx-l c) kt goal) #t)
               (for-all (lambda (h)
                          (or (not (eq? (car (force (car h))) 'vflex))   ; already determined by the indices
                              (let ([u (search c (cdr h) (- depth 1) (and conj (eq? k 'pair)))])
                                (and u (guard (x [(unify-failure? x) #f]) (unify (ctx-l c) (car h) (ev (ctx-env c) u)) #t)))))
                        (reverse holes))
               t)))))

(define (check c e ty) (with-pos e (lambda () (log-scope! c) (at-step e (check* c e ty)))))

;; A with-exec remembers where it is in the source, and the item in whose body it was built: if
;; the step fails, the runner says where; a run's report speaks with the program's names.
(define (at-step e t)
  (let ([p (and (pair? e) (hashtable-ref pos-of e #f))])
    (if (and p (memq (term-head t) '(Container.with-exec try-exec apply probe with-fresh-exec))) `(at ,(pos->vector p) ,t) t)))

(define (term-head t)
  (case (car t) [(app) (term-head (cadr t))] [(glob) (cadr t)] [else #f]))

;; A plan node carries, besides constructor and arguments, the step's position and its item.
(define (v-pos v) (and (> (length v) 3) (cadddr v)))
(define (v-name v) (and (> (length v) 4) (list-ref v 4)))
(define (v-question v) (and (> (length v) 5) (list-ref v 5)))
(define current-question (make-parameter #f))           ; the question (an item returning Remote Bool) in progress

;; An item is a definition of the program (not of the standard library) that produces a piece of
;; plan: while its body is evaluated, current-item holds its name. The arguments were already
;; evaluated by the caller, and stay the caller's.
;; An item with a docstring is shown by it, and lends it to the items without one it calls.
(define current-item (make-parameter #f))
(define plan-items (make-eq-hashtable))                  ; name → docstring, or #t
(define docs (make-eq-hashtable))                        ; name → the define's docstring
(define (item-doc n) (let ([d (hashtable-ref plan-items n #f)]) (and (string? d) d)))
(define (enter-item n) (if (and (not (item-doc n)) (current-item) (item-doc (current-item))) (current-item) n))
(define (plan-type? ty)                                  ; the result, after all arguments, is an Obj
  (let loop ([t (force ty)] [l 0])
    (case (car t)
      [(vpi) (loop (force (pi-cod t (vvar l))) (+ l 1))]
      [(vglob) (bi? (cadr t) 'obj)]
      [else #f])))

;; A question is an item returning an observation, (Remote Bool): in the report its docstring
;; stands in for the command it observes, below the item that asks it.
(define question-defs (make-eq-hashtable))
(define (question-type? ty)
  (let loop ([t (force ty)] [l 0])
    (case (car t)
      [(vpi) (loop (force (pi-cod t (vvar l))) (+ l 1))]
      [(vglob) (and (bi? (cadr t) 'obj) (pair? (caddr t))
                    (let ([k (force (caar (caddr t)))]) (and (eq? (car k) 'vglob) (eq? (cadr k) 'Kind.bool))))]
      [else #f])))
(define (question? n) (and (symbol? n) (hashtable-ref question-defs n #f) (item-doc n)))

(define (check* c e ty)
  (let ([want (force ty)])
    (cond [(eq? e 'TODO) (todo! c ty)]
          [(eq? e 'auto) (auto c ty)]
          [(head? e '%match) (check-match c e want)]
          [(let-form? e) (let-values ([(c body) (let-bind c e)]) (check c body ty))]
          [(lambda-form? e) (check-lambda c (cdr (cadr e)) (caddr e) ty)]
          [(and (string? e) (eq? (car want) 'vglob) (assq (hashtable-ref builtin-of (cadr want) #f) readers))
           => (lambda (r) (let ([vs ((cdr r) e)])          ; literal read by type, in context
                            (unless vs (oops "«~a» is not a valid ~a" e (cadr want)))   ; empty: no capture
                            (let* ([k (car (g-info (gget (cadr want))))]
                                   [n (length (explicit-args k))])
                              (check ctx0 `(,k ,@vs ,@(make-list (- n (length vs)) 'auto)) want))))]
          [(and (string? e) (eq? (car want) 'vglob) (bi? (cadr want) 'rel))   ; "bin/hello" is a vector
           (fold-left (lambda (acc seg) `(app (app (glob ,(bi 'step)) ,acc e) ,(check c seg `(vglob ,(bi 'segment) ())) e))
                      `(glob ,(bi 'here))
                      (filter (lambda (s) (not (string=? s ""))) (split-on e #\/)))]
          [(and (pair? e) (eq? (car e) '%br) (eq? (car want) 'vglob) (bi? (cadr want) 'list))
           (let ([a (car (car (caddr want)))] [l (ctx-l c)])  ; each element gets the expected type
             (fold-right (lambda (x acc) `(app (app (app (glob ,(bi 'cons)) ,(reify l a) i) ,(check c x a) e) ,acc e))
                         `(app (glob ,(bi 'nil)) ,(reify l a) i) (cdr e)))]
          [(and (pair? e) (symbol? (car e)) (gget (car e)) (not (known-local? c (car e))) (pair? (cdr e))
                (check-introduction c e want))
           => values]
          [else (check-inferred c e ty)])))

(define (known-local? c x) (or (index-of x (ctx-names c)) (assq x (ctx-defs c))))

;; (match e clause …) on a computed value: an auxiliary definition, f/matchN, that takes the
;; context and the scrutinee and does the cases; it goes through every define's checks (coverage, kernel).
;; The motive does not depend on the scrutinee: the cases refine neither the expected type nor the context.
;; The clauses do not call the define in progress: termination is checked define by define,
;; and a call inside the auxiliary would escape it.
(define defining (make-parameter '()))                   ; the defines in progress, innermost first
(define match-count 0)
(define (check-match c e want)
  (define (mentions-any? xs t) (if (pair? t) (exists (lambda (x) (mentions-any? xs x)) t) (and (symbol? t) (memq t xs))))
  (define (has-meta? t) (and (pair? t) (or (eq? (car t) 'meta) (exists has-meta? t))))
  (for-each (lambda (cl) (cond [(and (cadr cl) (mentions-any? (defining) (cadr cl)))
                                => (lambda (m) (oops "match on a computed value: it cannot call ~a, which is being defined; use match on the define's arguments" (car m)))]))
            (cddr e))
  (let* ([l (ctx-l c)]
         [scr (map (lambda (x) (call-with-values (lambda () (infer c x)) cons)) (cadr e))]
         [names (reverse (ctx-names c))]
         [defs (filter (lambda (d) (not (memq (car d) names))) (reverse (ctx-defs c)))]
         [binders (append (map (lambda (x a j) (list x (reify j a))) names (reverse (ctx-tys c)) (iota l))
                          (map (lambda (d) (list (car d) (reify l (caddr d)))) defs))]
         [k (length binders)]
         [ty (fold-right (lambda (b acc) `(pi ,(car b) e ,(cadr b) ,acc))
                         (fold-right (lambda (s j acc) `(pi _ e ,(reify (+ k j) (cdr s)) ,acc))
                                     (reify (+ k (length scr)) want) scr (iota (length scr)))
                         binders)]
         [pnames (let loop ([ns (map car binders)])     ; a name shadowed further on becomes _
                   (cond [(null? ns) '()]
                         [(memq (car ns) (cdr ns)) (cons '_ (loop (cdr ns)))]
                         [else (cons (car ns) (loop (cdr ns)))]))]
         [aux (begin (set! match-count (+ match-count 1))
                     (string->symbol (format "~a/match~a" (if (pair? (defining)) (car (defining)) 'match) match-count)))])
    (when (has-meta? ty) (oops "match: the type of the scrutinee or of the result is not known yet; annotate it with the"))
    (let ([saved (list pmetas absurds implicit-pmetas)])
      (check-def-core aux ty (map (lambda (cl) (cons (append pnames (car cl)) (cadr cl))) (cddr e)))
      (set! pmetas (car saved)) (set! absurds (cadr saved)) (set! implicit-pmetas (caddr saved)))
    (hashtable-delete! plan-items aux) (hashtable-delete! question-defs aux)   ; the steps belong to the item that uses it
    (fold-left (lambda (t a) `(app ,t ,a e)) `(glob ,aux)
               (append (map (lambda (j) `(var ,(- l 1 j))) (iota l)) (map (lambda (d) (reify l (cadr d))) defs) (map car scr)))))

;; An application of a global (an introduction, or a function like if) is checked against the expected type: first the
;; result type is unified with the expected one, then the arguments are checked in order, each
;; against its domain, known by then. (pair 2 refl) against (Σ Nat (λ [n] (≡ (+ n n) 4))).
;; So the expected type goes down into the arguments too: (if b (pair …) r) knows which Σ to build.
;; → term, or #f if the result does not match (falling back on inference, which gives the error).
(define (check-introduction c e want)
  (when (and (not (privileged)) (char=? (string-ref (symbol->string (car e)) 0) #\%))   ; as in infer
    (oops "~a is reserved to the core" (car e)))
  (let loop ([kt (g-type (gget (car e)))] [args (cdr e)] [spine '()])   ; spine: (meta-or-arg . visibility)
    (let ([kt (force kt)])
      (cond
        [(and (eq? (car kt) 'vpi) (or (eq? (caddr kt) 'i) (pair? args)))
         (let* ([m `(imeta ,(new-meta #f #f))] [mv (ev (ctx-env c) m)])
           (if (eq? (caddr kt) 'i)
               (loop (pi-cod kt mv) args (cons (list 'i m) spine))
               (loop (pi-cod kt mv) (cdr args) (cons (list 'e m mv (car args) (pi-dom kt)) spine))))]
        [(pair? args) #f]
        [(not (guard (x [(unify-failure? x) #f]) (unify (ctx-l c) kt want) #t)) #f]
        [else
         (fold-left (lambda (t s)
                      (if (eq? (car s) 'i)
                          `(app ,t ,(cadr s) i)
                          (let ([u (check c (list-ref s 3) (list-ref s 4))])
                            (guard (x [(unify-failure? x) (oops "~s: inconsistent argument" e)])
                              (unify (ctx-l c) (list-ref s 2) (ev (ctx-env c) u)))
                            `(app ,t ,u e))))
                    `(glob ,(car e))
                    (reverse spine))]))))

(define (check-inferred c e ty)
  (let*-values ([(t ty2) (infer c e)] [(t ty2) (insert c t ty2)])
    (or (guard (x [(unify-failure? x) #f]) (unify (ctx-l c) ty2 ty) t)
        (coerce c e t ty2 ty)
        (oops "~s: expected ~s, found ~s" e (show c ty) (show c ty2)))))

;; The literal stays, the type changes: if T has a constructor whose first field takes the value
;; and whose other fields are propositions, the value becomes (k value auto …). So
;; "golang:1.25-alpine" expected as an Image is the Σ pair (image "golang:1.25-alpine" proof).
(define (coerce c e t ty2 ty)
  (let ([want (force ty)])
    (and (eq? (car want) 'vglob) (null? (caddr want))
         (let ([g (gget (cadr want))])
           (and (eq? (g-kind g) 'data)
                (exists (lambda (k) (coerce-with c e t ty2 k (cadr want))) (g-info g)))))))

(define (coerce-with c e t ty2 k tname)
  (let ([kt (force (g-type (gget k)))])
    (and (eq? (car kt) 'vpi) (eq? (caddr kt) 'e)
         (guard (x [(unify-failure? x) #f]) (unify (ctx-l c) ty2 (pi-dom kt)) #t)
         (let loop ([tm `(app (glob ,k) ,t e)] [kt (force (pi-cod kt (ev (ctx-env c) t)))])
           (if (not (eq? (car kt) 'vpi))
               tm
               (let ([p (force (pi-dom kt))])
                 (cond [(not (and (eq? (car p) 'vglob) (memq (hashtable-ref builtin-of (cadr p) #f) '(unit eq empty)))) #f]
                       [(bi? (cadr p) 'empty) (oops "«~a» is not a valid ~a" (if (string? e) e (show c (ev (ctx-env c) t))) tname)]
                       [else (let ([pf (auto c p)]) (loop `(app ,tm ,pf e) (force (pi-cod kt (ev (ctx-env c) pf)))))])))))))

;; (λ [x y] body): checked against a Π. An implicit Π not named gets an implicit λ inserted by
;; itself, as in Agda: (the (→ {A Type} A A) (λ [x] x)).
(define (lambda-form? e)
  (and (pair? e) (eq? (car e) 'λ) (= (length e) 3) (pair? (cadr e)) (eq? (car (cadr e)) '%br)
       (for-all symbol? (cdr (cadr e)))))

(define (check-lambda c xs body ty)
  (if (null? xs)
      (check c body ty)
      (let ([want (force ty)])
        (unless (eq? (car want) 'vpi) (oops "λ: expected ~s, which is not a function" (show c ty)))
        (let* ([implicit (eq? (caddr want) 'i)] [x (if implicit '_ (car xs))]
               [body (check-lambda (bind c x (pi-dom want)) (if implicit xs (cdr xs)) body (pi-cod want (vvar (ctx-l c))))])
          `(lam ,(if implicit (cadr want) x) ,(caddr want) ,body)))))

;; (let [x e, y e2] body): bindings in sequence; x is a defined name, its value is substituted.
(define (let-form? e) (and (pair? e) (eq? (car e) 'let) (= (length e) 3) (pair? (cadr e)) (eq? (car (cadr e)) '%br)))
(define (let-bind c e)                                  ; → (values context body)
  (let loop ([c c] [bs (cdr (cadr e))])
    (cond [(null? bs) (values c (caddr e))]
          [(or (null? (cdr bs)) (not (symbol? (car bs)))) (oops "let: malformed bindings in ~s" e)]
          [else (let-values ([(t ty) (infer c (cadr bs))])
                  (loop (define-name c (car bs) (ev (ctx-env c) t) ty) (cddr bs)))])))

;; /out, /go/pkg/mod: a symbol starting with / is a point, (/ (/ root "go") "pkg") …
;; The term is built directly: a let binding root does not capture the literal.
(define (path-literal? e)
  (and (symbol? e) (let ([s (symbol->string e)]) (and (> (string-length s) 1) (char=? (string-ref s 0) #\/)))))
(define (path-term c e)
  (unless (bi 'abs) (oops "the path ~a needs paths: (import paths)" e))
  (fold-left (lambda (acc seg) `(app (app (glob ,(bi 'slash)) ,acc e) ,(check c seg `(vglob ,(bi 'segment) ())) e))
             `(glob ,(bi 'root))
             (filter (lambda (s) (not (string=? s ""))) (split-on (symbol->string e) #\/))))

(define (check-type c e)                                ; → (values term level)
  (let-values ([(t ty) (infer c e)])
    (let ([ty (force ty)])
      (case (car ty)
        [(vtype) (values t (cadr ty))]
        [(vflex) (unify (ctx-l c) ty '(vtype 0)) (values t 0)]  ; ponytail: unknown type ⇒ Type₀, no universe polymorphism
        [else (oops "~s is not a type" e)]))))

(define (elab-arrow c as)                               ; → (values term level)
  (if (null? (cdr as))
      (check-type c (car as))
      (let*-values ([(x a) (if (binder? (car as)) (values (cadar as) (caddar as)) (values '_ (car as)))]
                    [(ta na) (check-type c a)]
                    [(tb nb) (elab-arrow (bind c x (ev (ctx-env c) ta)) (cdr as))])
        (values `(pi ,x ,(if (and (pair? (car as)) (eq? (caar as) '%imp)) 'i 'e) ,ta ,tb) (max na nb)))))

;; Free variables of a signature, in order of first occurrence: they become implicit arguments.
;; In signatures only variable-shaped names quantify themselves: a letter, then digits (A, x, n2).
;; Any other free name is an unknown name: a Port without (import net) does not become any type.
(define (variable-shaped? x)
  (let ([cs (string->list (symbol->string x))])
    (and (char-alphabetic? (car cs)) (for-all char-numeric? (cdr cs)))))

(define (free-vars e)
  (let ([acc '()])
    (let walk ([e e] [bound '()])
      (cond
        [(symbol? e)
         (unless (or (memq e bound) (memq e acc) (gget e) (root-field e) (path-literal? e) (memq e '(→ Type _ TODO %br %imp pipe let auto λ the))) (if (variable-shaped? e) (set! acc (cons e acc)) (unknown-name e)))]
        [(lambda-form? e) (walk (caddr e) (append (cdr (cadr e)) bound))]   ; λ binds its names
        [(let-form? e)                                   ; let binds in sequence
         (let loop ([bs (cdr (cadr e))] [bound bound])
           (if (and (pair? bs) (pair? (cdr bs)))
               (begin (walk (cadr bs) bound) (loop (cddr bs) (cons (car bs) bound)))
               (walk (caddr e) bound)))]
        [(and (pair? e) (eq? (car e) '→))
         (let loop ([as (cdr e)] [bound bound])
           (cond [(null? as) (void)]
                 [(and (pair? (cdr as)) (binder? (car as)))
                  (walk (caddar as) bound) (loop (cdr as) (cons (cadar as) bound))]
                 [else (walk (car as) bound) (loop (cdr as) bound)]))]
        [(and (pair? e) (symbol? (car e)) (not (memq (car e) bound)) (not (gget (car e))) (pair? (qualified (car e))))
         (for-each (lambda (x) (walk x bound)) (cdr e))]   ; a short name at the head: resolved from the type
        [(pair? e) (for-each (lambda (x) (walk x bound)) e)]))
    (reverse acc)))

;; Signature → closed term. If the type of a free variable stays unknown it is generalized:
;; (≡ x x) becomes {x:type : Type}{x : x:type} → ≡ x x.
(define (elab-sig e)
  (let retry ([gen '()])
    (let* ([ms '()]
           [t (let go ([c ctx0] [vs (append (map cdr gen) (free-vars e))])
                (if (null? vs)
                    (let-values ([(t n) (check-type c e)]) t)
                    (let* ([x (car vs)]
                           [a (cond [(memq x (map cdr gen)) '(type 0)]
                                    [(assq x gen) => (lambda (p) (let-values ([(t n) (check-type c (cdr p))]) t))]
                                    [else (let ([m (new-meta x #f)]) (set! ms (cons (cons x m) ms)) `(imeta ,m))])])
                      `(pi ,x i ,a ,(go (bind c x (ev (ctx-env c) a)) (cdr vs))))))]
           [open (filter (lambda (p) (not (meta-sol (cdr p)))) ms)])
      (if (null? open)
          (zonked 0 '() t)
          (retry (append gen (map (lambda (p) (cons (car p) (string->symbol (format "~a:type" (car p))))) open)))))))

(define (zonk l env t)                                  ; substitutes the solved metavariables
  (case (car t)
    [(meta imeta) (reify l (ev env t))]
    [(app) `(app ,(zonk l env (cadr t)) ,(zonk l env (caddr t)) ,(cadddr t))]
    [(lam) `(lam ,(cadr t) ,(caddr t) ,(zonk (+ l 1) (cons (vvar l) env) (cadddr t)))]
    [(pi) `(pi ,(cadr t) ,(caddr t) ,(zonk l env (cadddr t)) ,(zonk (+ l 1) (cons (vvar l) env) (list-ref t 4)))]
    [(ann) `(ann ,(zonk l env (cadr t)) ,(zonk l env (caddr t)))]
    [(at) `(at ,(cadr t) ,(zonk l env (caddr t)))]
    [else t]))
(define (zonked l env t)
  (let ([z (zonk l env t)])
    (when (and (todos) (pair? (unbox (todos)))) (raise (quote todo-pending)))   ; a hole leaves metavariables: the clause is skipped
    (when (let has? ([z z]) (and (pair? z) (or (memq (car z) '(meta imeta)) (exists has? z))))
      (oops "cannot infer the implicit arguments in ~s" (sexp '() z)))
    z))

;; --- declarations ---

(define (check-decl d)
  (case (and (pair? d) (car d))
    [(data) (check-data d)]
    [(def) (check-def d)]
    [(extern) (check-extern d)]
    [(record) (for-each check-decl (record->decls d))]
    [(import) (for-each import! (cdr d))]
    [(builtin) (check-builtin d)]
    [else (oops "unknown declaration: ~s" d)]))

;; (import dagger time): the standard library's modules, lib/<name>.disegno, each loaded once.
;; They are checked as library (extern allowed); the name is a word, so a program cannot have
;; a file of its own loaded with those privileges. There is a single namespace.
;; ponytail: no qualified names and no selective imports; a cycle between modules stops silently.
(define imported (make-eq-hashtable))
(define (import! m)
  (unless (and (symbol? m) (for-all (lambda (c) (or (char-alphabetic? c) (char-numeric? c) (char=? c #\-)))
                                    (string->list (symbol->string m))))
    (oops "import: ~s is not a module name" m))
  (unless (hashtable-ref imported m #f)
    (let ([f (at-root (format "lib/~a.disegno" m))])
      (unless (file-exists? f) (oops "import: module ~a does not exist" m))
      (hashtable-set! imported m #t)
      (parameterize ([privileged #t]) (check-file f)))))

;; An unknown name that a module not yet imported declares says which import it needs.
;; ponytail: modules are scanned by reading their declarations, not by checking them; names
;; the generator produces (Container, with-exec…) are not found.
(define (unknown-name e)                                 ; at the atom, also from a walk of a signature
  (let ([m (module-of e)])
    (with-pos e (lambda () (if m
                               (oops "unknown name: ~a, it is in ~a: (import ~a)" e m m)
                               (oops "unknown name: ~a" e))))))

(define (module-of name)
  (find (lambda (m) (and (not (hashtable-ref imported m #f)) (memq name (declared-names m))))
        (map (lambda (f) (string->symbol (path-root f)))
             (list-sort string<? (filter (lambda (f) (equal? (path-extension f) "disegno")) (directory-list (at-root "lib")))))))

(define module-names (make-eq-hashtable))               ; module → names it declares
(define (declared-names m)
  (or (hashtable-ref module-names m #f)
      (let ([names (guard (e [#t '()])
                     (call-with-input-file (at-root (format "lib/~a.disegno" m))
                       (lambda (p) (let loop ([acc '()])
                                     (let ([d (read p)]) (if (eof-object? d) acc (loop (append (decl-names d) acc))))))))])
        (hashtable-set! module-names m names)
        names)))

(define (decl-names d)                                   ; names a claim, extern, data or record declares
  (if (and (pair? d) (memq (car d) '(claim extern data record)) (pair? (cdr d)))
      (let* ([head (cadr d)] [name (if (pair? head) (car head) head)]
             [clauses (filter symbol? (map (lambda (x) (and (pair? x) (car x))) (cddr d)))])
        (case (car d)
          [(data) (cons name clauses)]
          [(record) (cons name (map (lambda (f) (string->symbol (format "~a.~a" name f))) clauses))]
          [else (list name)]))
      '()))

;; (record Service [name : String] [replicas : Nat] [ok : (≥ replicas 1)]) is sugar for
;; a data with the single constructor service and the projections Service.name, Service.replicas, ...
;; In the types of later fields an earlier field f becomes (Service.f r).
;; With parameters: (record (Affine P V [≤ (→ P P Type)]) ...); a parameter without a type is a Type.
;; Parameters are implicit in the constructor and the projections.
(define (record->decls d)
  (let* ([head (cadr d)]
         [name (if (pair? head) (car head) head)]
         [params (if (pair? head)
                     (map (lambda (p) (if (symbol? p) (cons p 'Type) (cons (cadr p) (caddr p)))) (cdr head))
                     '())]
         [self (if (pair? head) (cons name (map car params)) name)]
         [imps (map (lambda (p) `(%imp ,(car p) ,(cdr p))) params)]
         [fields (map (lambda (f) (let ([f (unbracket f)])
                                    (unless (and (= (length f) 3) (eq? (cadr f) ':)) (oops "malformed field: ~s" f))
                                    (cons (car f) (caddr f))))
                      (cddr d))]
         [s (symbol->string name)]
         [k (string->symbol (string-append (string (char-downcase (string-ref s 0))) (substring s 1 (string-length s))))]
         [proj (lambda (f) (string->symbol (format "~a.~a" name f)))])
    (cons `(data ,name : ,(if (null? params) 'Type `(→ ,@(map (lambda (p) `(%br ,(car p) ,(cdr p))) params) Type))
             (%br ,k : (→ ,@imps ,@(map (lambda (f) `(%br ,(car f) ,(cdr f))) fields) ,self)))
          (let loop ([fs fields] [before '()] [i 0])
            (if (null? fs) '()
                (let ([ty (let subst ([e (cdar fs)])
                            (cond [(memq e before) `(,(proj e) %r)]
                                  [(pair? e) (map subst e)]
                                  [else e]))])
                  (cons `(def ,(proj (caar fs)) : (→ ,@imps (%br %r ,self) ,ty)
                           (%br (,k ,@(map (lambda (j) (if (= j i) '%v '_)) (iota (length fields))))) %v)
                        (loop (cdr fs) (cons (caar fs) before) (+ i 1)))))))))

;; (extern with-file : (→ [dir Dir] [path String] [contents String] Dir) Directory.withNewFile)
;; The field is Type.field (a method on the first argument) or a.b (a chain from the root); the
;; names of the explicit binders are the GraphQL argument names. An extern does not lie: it returns
;; an opaque engine type (Dir, Remote Bool…) or is a type itself; never a proposition nor a
;; string (that would be data from the world coming back into the language). The field can fix
;; arguments: (Container.withExec (expect ANY)). Pure primitives (prims) also return Bool: they compute, they do not observe.
(define (check-extern d)
  (unless (privileged) (oops "extern is reserved to the standard library"))
  (unless (and (= (length d) 5) (eq? (caddr d) ':)) (oops "malformed extern: ~s" d))
  (let* ([name (cadr d)] [spec (let ([f (list-ref d 4)]) (if (symbol? f) (list f) f))]
         [t (begin (fresh-name! name) (elab-sig (cadddr d)))])
    (k-type t)
    (let loop ([r t] [names '()])
      (if (eq? (car r) 'pi)
          (loop (list-ref r 4) (if (eq? (caddr r) 'e) (cons (cadr r) names) names))
          (let-values ([(h args) (spine-of r)])
            (unless (or (eq? (car r) 'type) (assq (car spec) prims)
                        (and (eq? (car h) 'glob) (not (bi? (cadr h) 'string)) (eq? (g-kind (gget (cadr h))) 'extern)))
              (oops "~a: an extern must return an opaque engine type" name))
            (define-global! name (make-g 'extern (ev '() t) (cons spec (reverse names)))))))))

;; --- positions: every list of the source remembers file and offset; errors report them ---

(define pos-of (make-eq-hashtable))                     ; list → (file . offset)
(define file-texts (make-hashtable string-hash string=?))

(define (with-pos e thunk)
  (cond [(and (pair? e) (hashtable-ref pos-of e #f)) => (lambda (p) (at-pos p thunk))]
        [(and (symbol? e) (here-counts) (pair? (here)))   ; an atom of the form at (here): its k-th child with that name
         (let ([k (hashtable-ref (here-counts) e 0)])
           (hashtable-set! (here-counts) e (+ k 1))
           (parameterize ([here (make-apos (car (here)) (cdr (here)) (symbol->string e) k)] [here-counts #f]) (thunk)))]
        [else (thunk)]))
(define (at-pos p thunk) (parameterize ([here p] [here-counts (make-eq-hashtable)]) (thunk)))

;; Atoms have no identity, so the reader cannot say where one is. An atom elaborated inside a
;; form is the k-th direct child of that form with its name, k counted while the form is
;; elaborated; failing that, its first occurrence in the form. Resolved only when asked for.
(define-record-type apos (fields file form name k))     ; form: offset of the enclosing form
(define here-counts (make-parameter #f))                ; name → atoms of the form at (here) seen so far

(define (pos-normal p)                                   ; → (file . offset)
  (if (apos? p)
      (let* ([atoms (cdr (scan-form (apos-file p) (apos-form p)))]
             [same (filter (lambda (t) (string=? (car t) (apos-name p))) atoms)]
             [direct (filter (lambda (t) (= (caddr t) 1)) same)])
        (cons (apos-file p) (cond [(> (length direct) (apos-k p)) (cadr (list-ref direct (apos-k p)))]
                                  [(pair? same) (cadr (car same))]
                                  [else (apos-form p)])))
      p))

;; The form starting at an offset, read as text: (end . atoms), each atom (name offset depth
;; forms), depth 1 for a direct child, forms the starts of the lists around it, innermost first.
;; Strings and comments are skipped.
(define form-scans (make-hashtable equal-hash equal?))
(define (scan-form file at)
  (let ([key (cons file at)])
    (or (hashtable-ref form-scans key #f)
        (let* ([text (hashtable-ref file-texts file "")] [n (string-length text)]
               [delim? (lambda (c) (or (char-whitespace? c) (memv c '(#\( #\) #\[ #\] #\" #\;))))]
               [r (if (and (< at n) (memv (string-ref text at) '(#\( #\[)))
                      (let loop ([i (+ at 1)] [forms (list at)] [acc '()])
                        (if (>= i n)
                            (cons n (reverse acc))
                            (let ([c (string-ref text i)])
                              (cond [(memv c '(#\( #\[)) (loop (+ i 1) (cons i forms) acc)]
                                    [(memv c '(#\) #\])) (if (null? (cdr forms)) (cons (+ i 1) (reverse acc)) (loop (+ i 1) (cdr forms) acc))]
                                    [(char=? c #\;) (loop (let skip ([j i]) (if (or (>= j n) (char=? (string-ref text j) #\newline)) j (skip (+ j 1)))) forms acc)]
                                    [(char=? c #\") (loop (let skip ([j (+ i 1)]) (cond [(>= j n) j] [(char=? (string-ref text j) #\\) (skip (+ j 2))]
                                                                                        [(char=? (string-ref text j) #\") (+ j 1)] [else (skip (+ j 1))]))
                                                          forms acc)]
                                    [(or (char-whitespace? c) (char=? c #\')) (loop (+ i 1) forms acc)]
                                    [else (let ([j (let word ([j i]) (if (and (< j n) (not (delim? (string-ref text j)))) (word (+ j 1)) j))])
                                            (loop j forms (cons (list (substring text i j) i (length forms) forms) acc)))]))))
                      (cons at '()))])
          (hashtable-set! form-scans key r)
          r))))

(define (form-head file at)                              ; the first atom of the form at an offset, if it opens with one
  (let ([a (find (lambda (t) (= (caddr t) 1)) (cdr (scan-form file at)))]
        [text (hashtable-ref file-texts file "")])
    (and a (let skip ([j (+ at 1)]) (cond [(= j (cadr a)) (car a)]
                                          [(char-whitespace? (string-ref text j)) (skip (+ j 1))]
                                          [else #f])))))

;; Where a binder binds: λ, define and match clauses bind in the form around its list (a clause
;; for a pattern), let, Π and ∀ one level further out. → (start . end), or #f.
(define (binder-scope file forms)
  (let* ([up (lambda (k) (and (> (length forms) k) (list-ref forms k)))]
         [head (lambda (k) (and (up k) (form-head file (up k))))]
         [s (cond [(member (head 2) '("let" "let*" "Π" "∀")) (up 2)]
                  [(member (head 1) '("λ" "lambda" "define")) (up 1)]
                  [else (let loop ([k 0]) (cond [(not (up (+ k 1))) #f]
                                                [(member (head (+ k 1)) '("match" "match*")) (up k)]
                                                [else (loop (+ k 1))]))])])
    (and s (cons s (car (scan-form file s))))))

;; --- what the LSP asks: the context of each elaborated term, and the binders of locals ---
;; scope-log, when set, collects (position ctx) for every term check and infer see.
(define scope-log (make-parameter #f))
(define (log-scope! c) (when (and (scope-log) (here)) (set-box! (scope-log) (cons (cons (here) c) (unbox (scope-log))))))

(define (scopes file)                                    ; → ((start end ctx name-or-#f) …), atoms and forms
  (filter values
    (map (lambda (s)
           (let ([p (pos-normal (car s))])
             (and (string=? (car p) file)
                  (if (apos? (car s))
                      (list (cdr p) (+ (cdr p) (string-length (apos-name (car s)))) (cdr s) (apos-name (car s)))
                      (list (cdr p) (car (scan-form file (cdr p))) (cdr s) #f)))))
         (unbox (scope-log)))))

(define (scope-at ss off)                                ; the smallest scope around off (an atom: off may be at its end)
  (fold-left (lambda (best s)
               (if (and (<= (car s) off) (or (< off (cadr s)) (and (cadddr s) (= off (cadr s))))
                        (or (not best) (< (- (cadr s) (car s)) (- (cadr best) (car best)))))
                   s best))
             #f ss))

(define (ctx-locals c)                                   ; → ((name . type-string) …), let first, then binders, innermost first
  (let* ([l (ctx-l c)] [names (ctx-names c)]
         [lets (map (lambda (d) (cons (symbol->string (car d)) (render-term names (reify l (caddr d))))) (ctx-defs c))])
    (let loop ([i 0] [seen (map (lambda (d) (car d)) (ctx-defs c))] [acc (reverse lets)])
      (if (= i l)
          (reverse acc)
          (let ([x (list-ref names i)])
            (if (and (symbol? x) (not (memq x seen)) (not (char=? (string-ref (symbol->string x) 0) #\%)) (not (eq? x '_)))
                (loop (+ i 1) (cons x seen)
                      (cons (cons (symbol->string x) (render-term (list-tail names (+ i 1)) (reify (- l i 1) (list-ref (ctx-tys c) i)))) acc))
                (loop (+ i 1) seen acc)))))))

(define (offset-at file line col)                        ; line and col from 0, as the LSP counts
  (let ([text (hashtable-ref file-texts file "")])
    (let loop ([i 0] [l 0])
      (cond [(= l line) (min (+ i col) (string-length text))]
            [(>= i (string-length text)) i]
            [else (loop (+ i 1) (if (char=? (string-ref text i) #\newline) (+ l 1) l))]))))

(define (locals-at file off)                             ; the locals in scope at off
  (let ([s (scope-at (scopes file) off)]) (if s (ctx-locals (caddr s)) '())))

;; The binder of a local: the last occurrence of its name before the use, in the same top-level
;; declaration, that was not elaborated as a term and whose binding form contains the use.
(define decl-starts (make-hashtable string-hash string=?))   ; file → offsets of its declarations
(define (binder-of file use name)
  (let* ([ss (scopes file)]
         [uses (map car (filter (lambda (s) (equal? (cadddr s) name)) ss))]
         [start (fold-left (lambda (b d) (if (and (<= d use) (> d b)) d b)) 0 (hashtable-ref decl-starts file '()))]
         [cands (filter (lambda (t) (and (string=? (car t) name) (< (cadr t) use) (not (memv (cadr t) uses))
                                         (let ([s (binder-scope file (cadddr t))]) (and s (< (car s) use (cdr s))))))
                        (cdr (scan-form file start)))])
    (and (pair? cands) (cadr (list-ref cands (- (length cands) 1))))))

;; A local at off, used or bound there: (type-string . binder-offset), or #f.
(define (local-at file off name)
  (let* ([ss (scopes file)] [s (scope-at ss off)])
    (if (and s (equal? (cadddr s) name))
        (let ([t (assoc name (ctx-locals (caddr s)))])
          (and t (cons (cdr t) (binder-of file (car s) name))))
        (exists (lambda (u) (and (equal? (cadddr u) name) (> (car u) off) (eqv? (binder-of file (car u) name) (car (word-start file off)))
                                 (let ([t (assoc name (ctx-locals (caddr u)))]) (and t (cons (cdr t) (car (word-start file off)))))))
                (reverse ss)))))

(define (word-start file off)                            ; (start . end) of the atom around off
  (let* ([text (hashtable-ref file-texts file "")] [n (string-length text)]
         [delim? (lambda (c) (or (char-whitespace? c) (memv c '(#\( #\) #\[ #\] #\" #\; #\'))))])
    (cons (let loop ([j (min off n)]) (if (and (> j 0) (not (delim? (string-ref text (- j 1))))) (loop (- j 1)) j))
          (let loop ([j (min off n)]) (if (and (< j n) (not (delim? (string-ref text j)))) (loop (+ j 1)) j)))))

(define (pos->string p)                                  ; → "file:line:col"
  (let ([v (pos->vector p)]) (format "~a:~a:~a" (vector-ref v 0) (vector-ref v 1) (vector-ref v 2))))

(define (pos->vector p)                                  ; → #(file line col)
  (let* ([p (pos-normal p)] [text (hashtable-ref file-texts (car p) "")])
    (let loop ([i 0] [line 1] [col 1])
      (if (or (>= i (cdr p)) (>= i (string-length text)))
          (vector (car p) line col)
          (if (char=? (string-ref text i) #\newline) (loop (+ i 1) (+ line 1) 1) (loop (+ i 1) line (+ col 1)))))))

;; From annotation to s-expression: every list remembers where it is in the file. The reader is
;; Scheme's: [..] is a synonym of (..), as in R6RS.
(define (strip file a)
  (if (not (annotation? a))
      a
      (let ([e (annotation-expression a)] [at (source-object-bfp (annotation-source a))])
        (if (pair? e)
            (let ([d (let loop ([e e]) (cond [(pair? e) (cons (strip file (car e)) (loop (cdr e)))]
                                             [(null? e) '()]
                                             [else (strip file e)]))])
              (hashtable-set! pos-of d (cons file at))
              d)
            e))))

;; --- the surface: Scheme with types, like Pie ---
;; (claim f T) and (define (f x …) body); (Π ((x A) …) B), (∀ ((A Type) …) B) for implicits;
;; (λ (x …) body); (let ((x e) …) body), in sequence; (list a b); (match x (p body) …) and
;; (match* (x y) ((p q) body) …) on the arguments; cond, when, unless, begin, string-append.
;; Everything becomes the elaborator's internal forms: (%br …) for lists, binders and bindings.

(define (keep new old)                                   ; the new form inherits the position
  (let ([p (and (pair? old) (hashtable-ref pos-of old #f))])
    (when (and p (pair? new) (not (hashtable-ref pos-of new #f))) (hashtable-set! pos-of new p))
    new))

(define (head? e h) (and (pair? e) (eq? (car e) h)))
(define (bindings who bs)                                ; ((x e) …) → ((x . e) …)
  (unless (and (list? bs) (for-all (lambda (b) (and (list? b) (= (length b) 2) (symbol? (car b)))) bs))
    (oops "~a: malformed bindings in ~s" who bs))
  (map (lambda (b) (cons (car b) (cadr b))) bs))

(define (sx e)                                           ; surface expression → internal form
  (if (pair? e) (with-pos e (lambda () (keep (sx* e) e))) e))
(define (sx* e)
  (unless (list? e) (oops "invalid expression: ~s" e))
  (case (car e)
    [(Π ∀) (unless (= (length e) 3) (oops "~a: (~a ((x A) …) B)" (car e) (car e)))
     `(→ ,@(map (lambda (b) `(,(if (eq? (car e) 'Π) '%br '%imp) ,(car b) ,(sx (cdr b)))) (bindings (car e) (cadr e)))
         ,(sx (caddr e)))]
    [(λ lambda) (unless (and (= (length e) 3) (list? (cadr e)) (for-all symbol? (cadr e))) (oops "λ: (λ (x …) body)"))
     `(λ (%br ,@(cadr e)) ,(sx (caddr e)))]
    [(let let*) (unless (= (length e) 3) (oops "let: (let ((x e) …) body)"))
     `(let (%br ,@(apply append (map (lambda (b) (list (car b) (sx (cdr b)))) (bindings 'let (cadr e))))) ,(sx (caddr e)))]
    [(list) `(%br ,@(map sx (cdr e)))]
    [(cond) (let loop ([cs (cdr e)])
              (cond [(null? cs) (oops "cond: else is missing")]
                    [(not (and (list? (car cs)) (= (length (car cs)) 2))) (oops "cond: malformed clause ~s" (car cs))]
                    [(eq? (caar cs) 'else) (unless (null? (cdr cs)) (oops "cond: else goes last")) (sx (cadar cs))]
                    [else (keep `(if ,(sx (caar cs)) ,(sx (cadar cs)) ,(loop (cdr cs))) (car cs))]))]
    [(when unless) (unless (= (length e) 3) (oops "~a: (~a observation body)" (car e) (car e)))
     (if (eq? (car e) 'when) `(branch ,(sx (cadr e)) ,(sx (caddr e)) skip) `(branch ,(sx (cadr e)) skip ,(sx (caddr e))))]
    [(begin) (when (null? (cdr e)) (oops "empty begin"))
     (let loop ([xs (cdr e)]) (if (null? (cdr xs)) (sx (car xs)) `(then ,(sx (car xs)) ,(loop (cdr xs)))))]
    [(string-append) (if (null? (cdr e)) ""
                         (let loop ([xs (cdr e)]) (if (null? (cdr xs)) (sx (car xs)) `(concat ,(sx (car xs)) ,(loop (cdr xs))))))]
    [(match match*)                                      ; on any value: check-match elaborates it
     (unless (>= (length e) 3) (oops "~a: (~a x clause …)" (car e) (car e)))
     (let ([xs (if (eq? (car e) 'match) (list (cadr e)) (cadr e))])
       (unless (list? xs) (oops "match*: (match* (x y) ((p q) body) …)"))
       `(%match ,(map sx xs)
                ,@(map (lambda (cl) (let-values ([(ps b) (split-clause cl (length xs))]) (list ps (and b (sx b)))))
                       (cddr e))))]
    [(claim define data record extern import builtin) (oops "~a: it is a declaration, not an expression" (car e))]
    [else (map sx e)]))

;; A clause's patterns: the variables are the leaves, except a constructor's head.
(define (pattern-var? x pats)
  (let walk ([ps pats])
    (exists (lambda (p) (if (pair? p) (walk (cdr p)) (eq? p x))) ps)))
(define (subst-pats pats xs qs)                          ; all together: (match* (m n) ((n m) …)) swaps
  (map (lambda (p) (cond [(and (symbol? p) (memq p xs)) (list-ref qs (- (length xs) (length (memq p xs))))]
                         [(pair? p) (cons (car p) (subst-pats (cdr p) xs qs))]
                         [else p]))
       pats))

;; (match x clause …) at the head of the body: x becomes each clause's pattern, and so on
;; inside. → list of (patterns . body); body #f for an absurd clause, (p) without a body.
;; On anything other than the arguments it is an expression: check-match elaborates it.
(define (split-clause cl n)                              ; → (values patterns-of-each body-or-#f)
  (unless (and (list? cl) (<= 1 (length cl) 2)) (oops "match: malformed clause ~s" cl))
  (let ([ps (if (= n 1) (list (car cl)) (car cl))])
    (unless (and (list? ps) (= (length ps) n)) (oops "match*: ~a patterns expected in ~s" n cl))
    (values ps (and (pair? (cdr cl)) (cadr cl)))))
(define (expand-clauses pats body)
  (define (on-args? xs) (and (list? xs) (for-all (lambda (x) (and (symbol? x) (pattern-var? x pats))) xs)))
  (cond
    [(and (or (head? body 'match) (head? body 'match*)) (pair? (cdr body))
          (on-args? (if (eq? (car body) 'match) (list (cadr body)) (cadr body))))
     (let ([xs (if (eq? (car body) 'match) (list (cadr body)) (cadr body))])
       (with-pos body
         (lambda ()
           (apply append
             (map (lambda (cl)
                    (let-values ([(ps b) (split-clause cl (length xs))])
                      (let ([pats (subst-pats pats xs ps)])
                        (if b (expand-clauses pats b) (list (cons pats #f))))))
                  (cddr body))))))]
    [else (list (cons pats (sx body)))]))

;; A data of constructors without arguments only has its D.name : (→ D String), the name of the
;; constructor: the inverse of Host-choice. Only where String exists already (after the prelude).
(define (name-def d ks)
  (let ([ks (map (lambda (k) (if (and (pair? k) (null? (cdr k))) (car k) k)) ks)])
    (if (and (pair? ks) (for-all symbol? ks) (bi 'string))
        (list `(def ,(string->symbol (format "~a.name" d)) : (→ ,d ,(bi 'string))
                 ,@(apply append (map (lambda (k) (list `(%br ,k) (symbol->string k))) ks))))
        '())))

(define claims (make-parameter (make-eq-hashtable)))      ; claim → signature, waiting for its define; one per file

(define (desugar-decl d)                                 ; → internal declarations
  (define (need n) (unless (and (list? d) (>= (length d) n)) (oops "malformed ~a: ~s" (car d) d)))
  (case (and (pair? d) (car d))
    [(claim) (need 3)
     (unless (and (= (length d) 3) (symbol? (cadr d))) (oops "claim: (claim name type)"))
     (when (hashtable-ref (claims) (cadr d) #f) (oops "~a: already claimed, the define is missing" (cadr d)))
     (hashtable-set! (claims) (cadr d) (sx (caddr d)))
     (hashtable-set! claim-pos (cadr d) (hashtable-ref pos-of d #f))
     '()]
    [(define) (need 3)
     (unless (or (= (length d) 3) (and (= (length d) 4) (string? (caddr d)))) (oops "define: (define (name x …) body)"))
     (let* ([h (cadr d)] [name (if (pair? h) (car h) h)] [params (if (pair? h) (cdr h) '())]
            [d (if (= (length d) 4)                     ; the docstring, as in Scheme: the item's label
                   (begin (hashtable-set! docs name (caddr d)) (list (car d) h (cadddr d)))
                   (begin (hashtable-delete! docs name) d))]
            [t (or (hashtable-ref (claims) name #f) (oops "~a: the claim is missing, (claim ~a type)" name name))])
       (hashtable-delete! (claims) name)
       (list (if (null? params)
                 `(def ,name : ,t ,(sx (caddr d)))
                 `(def ,name : ,t ,@(apply append (map (lambda (c) (if (cdr c) (list `(%br ,@(car c)) (cdr c)) (list `(%br ,@(car c)))))
                                                       (expand-clauses params (caddr d))))))))]
    [(data) (need 2)
     (if (and (pair? (cddr d)) (eq? (caddr d) ':))
         (begin (need 4)
                (list `(data ,(cadr d) : ,(sx (cadddr d))
                         ,@(map (lambda (k) (unless (and (list? k) (= (length k) 3) (eq? (cadr k) ':)) (oops "malformed constructor: ~s" k))
                                  (keep `(%br ,(car k) : ,(sx (caddr k))) k))
                                (list-tail d 4)))))
         (cons `(data ,(cadr d)
                  ,@(map (lambda (k) (cond [(symbol? k) `(%br ,k)]
                                           [(and (list? k) (pair? k) (symbol? (car k))) (keep `(%br ,(car k) ,@(map sx (cdr k))) k)]
                                           [else (oops "malformed constructor: ~s" k)]))
                         (cddr d)))
               (name-def (cadr d) (cddr d))))]
    [(record) (need 2)
     (let ([h (cadr d)])
       (list `(record ,(if (pair? h)
                           (cons (car h) (map (lambda (p) (if (symbol? p) p `(%br ,@(car (map (lambda (b) (list (car b) (sx (cdr b)))) (bindings 'record (list p)))))))
                                              (cdr h)))
                           h)
                ,@(map (lambda (f) (let ([b (car (bindings 'record (list f)))]) (keep `(%br ,(car b) : ,(sx (cdr b))) f))) (cddr d)))))]
    [(extern) (unless (and (list? d) (= (length d) 5) (eq? (caddr d) ':)) (oops "malformed extern: ~s" d))
     (list `(extern ,(cadr d) : ,(sx (cadddr d)) ,(list-ref d 4)))]
    [(import builtin) (list d)]
    [(def) (oops "def is gone: (claim name type) and then (define (name x …) body)")]
    [else (oops "unknown declaration: ~s" d)]))

(define (check-text name text) (parameterize ([claims (make-eq-hashtable)]) (check-text* name text)))
(define (check-text* name text)
  (hashtable-set! file-texts name text)
  (let ([sfd (make-source-file-descriptor name (open-bytevector-input-port (string->utf8 text)))]
        [p (open-string-input-port text)])
    ;; An error does not stop the file: the next declaration is checked anyway, and at the end
    ;; the errors come out together, one per line. A define whose body is wrong stays known by
    ;; its claim; the "unknown name" errors of a name whose declaration failed are silenced.
    (let loop ([bfp 0] [errs '()] [failed '()])
      (let-values ([(a next) (get-datum/annotations p sfd bfp)])
        (if (eof-object? a)
            (let ([errs (append (map (lambda (n) (format "~a: claim without define" n)) (vector->list (hashtable-keys (claims)))) errs)])
              (unless (null? errs)
                (error 'disegno (fold-left (lambda (acc m) (string-append m "\n" acc)) (car errs) (cdr errs)))))
            (let* ([d (strip name a)]
                   [_ (let ([p (hashtable-ref pos-of d #f)]) (when p (hashtable-update! decl-starts name (lambda (l) (cons (cdr p) l)) (quote ()))))]
                   [m (guard (e [(and (who-condition? e) (eq? (condition-who e) 'disegno) (message-condition? e)) (condition-message e)])
                        (with-pos d (lambda () (for-each (lambda (i) (with-pos (keep i d) (lambda () (check-decl i)))) (desugar-decl d))))
                        #f)]
                   [cascade? (and m (exists (lambda (n) (let ([s (format "unknown name: ~a" n)])
                                                           (and (>= (string-length m) (string-length s))
                                                                (string=? s (substring m (- (string-length m) (string-length s)) (string-length m))))))
                                            failed))])
              (loop next (if (and m (not cascade?)) (cons m errs) errs)
                    (if (and m (pair? d) (pair? (cdr d))) (cons (let ([n (cadr d)]) (if (pair? n) (car n) n)) failed) failed))))))))

;; Relative paths resolve against the directory of the file that names them.
(define current-dir (make-parameter ""))
(define (in-dir dir p) (if (or (string=? dir "") (path-absolute? p)) p (string-append dir "/" p)))

(define (check-file path)
  (parameterize ([current-dir (path-parent path)])
    (check-text path (call-with-port (open-file-input-port path (file-options) (buffer-mode block) (make-transcoder (utf-8-codec)))
                       get-string-all))))
(define (check-string s) (check-text "<string>" s))

;; (data Nat [zero] [add1 Nat])  or  (data Vec : (→ Type Nat Type) [nil : (Vec A 0)] ...)
(define (check-data d)
  (let*-values ([(name) (cadr d)]
                [(sig ks) (if (and (pair? (cddr d)) (eq? (caddr d) ':))
                              (values (cadddr d) (map (lambda (k) (let ([k (unbracket k)]) (cons (car k) (caddr k)))) (list-tail d 4)))
                              (values 'Type (map (lambda (k) (let ([k (unbracket k)])
                                                               (cons (car k) (if (null? (cdr k)) name `(→ ,@(cdr k) ,name)))))
                                                 (cddr d))))])
    (fresh-name! name)
    (let* ([t (elab-sig sig)] [n (begin (k-type t) (data-level (ev '() t)))])
      (define-global! name (make-g 'data (ev '() t) '()))
      (let* ([cts (map (lambda (k) (fresh-name! (car k)) (elab-sig (cdr k))) ks)]
             [teles (map (lambda (k ct) (telescope name (car k) ct)) ks cts)]
             [params (param-positions teles)])
        (for-each (lambda (k tele) (check-con name n params (car k) tele)) ks teles)
        (for-each (lambda (k ct raw) (with-pos raw (lambda () (define-global! (car k) (make-g 'con (ev '() ct) name)))))
                  ks cts (if (and (pair? (cddr d)) (eq? (caddr d) ':)) (list-tail d 4) (cddr d)))
        (g-info-set! (gget name) (map car ks))))))

(define (data-level v)
  (let loop ([v (force v)] [l 0])
    (case (car v)
      [(vpi) (loop (force (pi-cod v (vvar l))) (+ l 1))]
      [(vtype) (cadr v)]
      [else (oops "the type of a data must end in Type")])))

;; → (binders . spine of the return type); binder = (visibility level normalized-domain)
(define (telescope d k t)
  (k-type t)
  (let loop ([env '()] [tys '()] [l 0] [t t] [bs '()])
    (if (eq? (car t) 'pi)
        (let ([va (ev env (cadddr t))])
          (loop (cons (vvar l) env) (cons va tys) (+ l 1) (list-ref t 4)
                (cons (list (caddr t) (k-level (k-infer env tys l (cadddr t))) (reify l va)) bs)))
        (let ([r (force (ev env t))])
          (unless (and (eq? (car r) 'vglob) (eq? (cadr r) d)) (oops "constructor ~a must return ~a" k d))
          (cons (reverse bs) (caddr r))))))

;; Parameter: a position held in every constructor by a bare implicit variable (A in Vec A n).
(define (param-positions teles)
  (if (null? teles) '()
      (filter (lambda (p)
                (for-all (lambda (tl)
                           (let ([v (force (car (list-ref (cdr tl) p)))])
                             (and (eq? (car v) 'vrigid) (null? (caddr v)) (eq? 'i (car (list-ref (car tl) (cadr v)))))))
                         teles))
              (iota (length (cdr (car teles)))))))

(define (check-con d n params k tele)
  (let ([exempt (map (lambda (p) (cadr (force (car (list-ref (cdr tele) p))))) params)])
    (let loop ([bs (car tele)] [l 0])
      (unless (null? bs)
        (unless (or (memv l exempt) (<= (cadr (car bs)) n))
          (oops "~a: a field of level ~a does not fit in ~a, of level ~a" k (cadr (car bs)) d n))
        (unless (strictly-positive? d (caddr (car bs)))
          (oops "~a: ~a does not occur strictly positively" k d))
        (loop (cdr bs) (+ l 1))))
    (for-each (lambda (a) (when (mentions? d (reify (length (car tele)) (car a))) (oops "~a: ~a in its own indices" k d)))
              (cdr tele))))

(define (mentions? d t) (or (equal? t `(glob ,d)) (and (pair? t) (exists (lambda (x) (mentions? d x)) t))))
(define (spine-of t)
  (let loop ([t t] [args '()]) (if (eq? (car t) 'app) (loop (cadr t) (cons (caddr t) args)) (values t args))))
(define (strictly-positive? d t)
  (or (not (mentions? d t))
      (and (eq? (car t) 'pi) (not (mentions? d (cadddr t))) (strictly-positive? d (list-ref t 4)))
      (let-values ([(h args) (spine-of t)])
        (or (and (equal? h `(glob ,d)) (not (exists (lambda (a) (mentions? d a)) args)))
            ;; Nested in a list: (List (Obj k)) is fine, because List is strictly positive in its
            ;; parameter (as in Coq and Agda). Only the builtin's List.
            (and (bi 'list) (equal? h `(glob ,(bi 'list))) (= (length args) 1) (strictly-positive? d (car args)))))))

;; (def f : T [p ...] body ...)  or  (def f : T body)
;; A clause with an absurd pattern () has no body: [(⊑-step ())].
(define (check-def d)
  (unless (and (>= (length d) 4) (eq? (caddr d) ':)) (oops "malformed def: ~s" d))
  (let ([name (cadr d)])
    (fresh-name! name)
    (check-def-core name (let ([p (hashtable-ref claim-pos name #f)])   ; the signature, where the claim is
                           (if p (at-pos p (lambda () (elab-sig (cadddr d)))) (elab-sig (cadddr d))))
                    (parse-clauses name (list-tail d 4)))))
(define claim-pos (make-eq-hashtable))                  ; name → position of its claim

(define (absurd? p) (or (null? p) (and (pair? p) (exists absurd? (cdr p)))))
(define (absurd-clause? x) (and (pair? x) (eq? (car x) '%br) (exists absurd? (cdr x))))

(define (parse-clauses name rest)                       ; → list of (patterns . body); body #f if absurd
  (cond [(null? rest) (oops "~a: the definition is missing" name)]
        [(and (null? (cdr rest)) (not (absurd-clause? (car rest)))) (list (cons '() (car rest)))]
        [else (let loop ([r rest])
                (cond [(null? r) '()]
                      [(absurd-clause? (car r)) (cons (cons (cdr (car r)) #f) (loop (cdr r)))]
                      [(null? (cdr r)) (oops "~a: clause without a body" name)]
                      [else (cons (cons (unbracket (car r)) (cadr r)) (loop (cddr r)))]))]))

(define (check-def-core name t clauses)
  (let ([ty (begin (k-type t) (ev '() t))])
    (define-global! name (make-g 'def ty #f))
    (hashtable-set! sigs name t)
    (when (and (not (privileged)) (plan-type? ty)) (hashtable-set! plan-items name (hashtable-ref docs name #t)))
    (hashtable-set! question-defs name (question-type? ty))
    (let* ([pats (map (lambda (c) (map norm-pat (car c))) clauses)]
           [_ (unless (apply = (map length pats)) (oops "~a: the clauses have different numbers of patterns" name))]
           [checked (parameterize ([todos (box '())] [defining (cons name (defining))])
                      (let ([r (map (lambda (ps c) (guard (x [(eq? x 'todo-pending) '(#f)])   ; the other clauses' holes, then all together
                                                      (check-clause name ty ps (cdr c))))
                                    pats clauses)])   ; (clause . resolved syntax)
                        (flush-todos!)
                        r))]
           [cs (filter values (map car checked))])
      (cover name ty (map cdr checked))
      (terminates! name cs)
      (g-info-set! (gget name) (if (null? cs) '(0) (cons (length (car (car cs))) cs))))))

(define (norm-pat p)
  (cond [(null? p) '()]                                  ; absurd pattern
        [(nat? p) (if (zero? p) '(zero) `(add1 ,(norm-pat (- p 1))))]
        [(symbol? p) p]                                  ; variable or constructor: the type decides (check-pat)
        [(and (pair? p) (con? (car p))) (cons (car p) (map norm-pat (cdr p)))]
        [else (oops "invalid pattern: ~s" p)]))

;; Phase A: patterns are checked with variables as closed metavariables, so unification of the
;; indices solves them (forced patterns).
;; → (values trees remaining-type explicit-trees); the explicit ones are for coverage.
;; The signature's implicits take the name of their binder ({X Type} → X in the body), unless
;; that name is used by a pattern of the clause: then the pattern wins.
(define implicit-pmetas '())
(define (check-pats ty pats)
  (define used (let flat ([p pats]) (cond [(symbol? p) (list p)] [(pair? p) (append (flat (car p)) (flat (cdr p)))] [else '()])))
  (let loop ([ty ty] [pats pats] [trees '()] [explicit '()])
    (if (null? pats)
        (values (reverse trees) ty (reverse explicit))
        (let ([ty (force ty)])
          (unless (eq? (car ty) 'vpi) (oops "too many patterns"))
          (if (eq? (caddr ty) 'i)
              (let ([m (new-pmeta (if (memq (cadr ty) used) '_ (cadr ty)) (pi-dom ty))])
                (set! implicit-pmetas (cons m implicit-pmetas))
                (loop (pi-cod ty (meta-val m)) pats (cons `(pmeta ,m) trees) explicit))
              (let-values ([(tree v) (check-pat (car pats) (pi-dom ty))])
                (loop (pi-cod ty v) (cdr pats) (cons tree trees) (cons tree explicit))))))))

;; The resolved syntax of a tree, for coverage: variables stay symbols, constructors become
;; (c explicit-arguments…).
(define (tree->syn tr)
  (case (car tr)
    [(pmeta) (or (meta-name (cadr tr)) '_)]
    [(pcon) (cons (cadr tr)
                  (let loop ([kt (force (g-type (gget (cadr tr))))] [ts (caddr tr)] [l 0])
                    (cond [(or (null? ts) (not (eq? (car kt) 'vpi))) '()]
                          [(eq? (caddr kt) 'e) (cons (tree->syn (car ts)) (loop (force (pi-cod kt (vvar l))) (cdr ts) (+ l 1)))]
                          [else (loop (force (pi-cod kt (vvar l))) (cdr ts) (+ l 1))])))]))

;; A symbol in a pattern is a constructor only if it is a constructor of the expected type: so
;; [port] or [step] stay variables where a Nat or a function is expected.
(define (constructor-here? p ty)
  (and (con? p)
       (let ([v (force ty)])
         (case (car v)
           [(vglob) (eq? (g-info (gget p)) (cadr v))]
           [(vflex) #t]                                  ; type still unknown: the name wins
           [else #f]))))

;; Absurd pattern: the position has no values. It is verified after unifying all the clause's
;; patterns (absurd-check!), when the type is determined: every constructor must conflict with
;; the indices.
(define absurds '())

(define (absurd-check! ty)
  (let ([v (force ty)])
    (unless (and (eq? (car v) 'vglob) (eq? (g-kind (gget (cadr v))) 'data))
      (oops "() needs an inductive type, not ~s" (sexp '() (reify 0 v))))
    (for-each (lambda (k)
                (let* ([saved-pm pmetas] [saved (map (lambda (m) (cons m (meta-sol m))) pmetas)]
                       [r (guard (x [(unify-failure? x) (unify-failure-kind x)])
                            (call-with-values (lambda () (check-pat (cons k (map (lambda (_) '_) (explicit-args k))) v))
                                              (lambda _ 'ok)))])
                  (for-each (lambda (s) (solve! (car s) (cdr s))) saved)  ; the attempt leaves no trace
                  (set! pmetas saved-pm)
                  (unless (eq? r 'conflict) (oops "() is not absurd: ~a is possible in ~s" k (sexp '() (reify 0 v))))))
              (g-info (gget (cadr v))))))

(define (check-pat p ty)                                ; → (values tree value)
  (cond
    [(null? p) (set! absurds (cons ty absurds)) (let ([m (new-pmeta '_ ty)]) (values `(pmeta ,m) (meta-val m)))]
    [else (check-pat1 p ty)]))

(define (check-pat1 p ty)
  (if (and (symbol? p) (constructor-here? p ty))
      (check-pat1 (list p) ty)
      (check-pat2 p ty)))

(define (check-pat2 p ty)
  (if (symbol? p)
      (let ([m (new-pmeta p ty)]) (values `(pmeta ,m) (meta-val m)))
      (let loop ([kty (g-type (gget (car p)))] [ps (cdr p)] [trees '()] [sp '()])
        (let ([kty (force kty)])
          (cond
            [(and (eq? (car kty) 'vpi) (eq? (caddr kty) 'i))
             (let ([m (new-pmeta '_ (pi-dom kty))])
               (loop (pi-cod kty (meta-val m)) ps (cons `(pmeta ,m) trees) (cons (cons (meta-val m) 'i) sp)))]
            [(and (eq? (car kty) 'vpi) (pair? ps))
             (let-values ([(tree v) (check-pat (car ps) (pi-dom kty))])
               (loop (pi-cod kty v) (cdr ps) (cons tree trees) (cons (cons v 'e) sp)))]
            [(or (eq? (car kty) 'vpi) (pair? ps)) (oops "wrong number of arguments in ~s" p)]
            [else (unify 0 kty ty)
                  (values `(pcon ,(car p) ,(reverse trees)) `(vglob ,(car p) ,(reverse sp)))])))))

;; Phase B: the unsolved variables become the context (in dependency order), the solved ones
;; become defined names. Then the body: elaborated, zonked, rechecked by the kernel.
(define (check-clause f ty pats body)
  (set! pmetas '())
  (set! absurds '())
  (set! implicit-pmetas '())
  (let-values ([(trees rest explicit) (guard (x [(unify-failure? x) (oops "~a: the case ~s is impossible or ill-typed" f (cons f pats))])
                                        (check-pats ty pats))])
    (for-each absurd-check! absurds)
    (let ([syn (map tree->syn explicit)])                 ; → (run-time-clause . resolved syntax)
      (if (not body)
          (begin (when (null? absurds) (oops "~a: clause ~s without a body and without ()" f pats)) (cons #f syn))
          (cons (check-clause-body f pats body trees rest) syn)))))

(define (check-clause-body f pats body trees rest)
  (begin
    (let* ([named (filter (lambda (x) (not (eq? x '_))) (map meta-name (filter (lambda (m) (not (memv m implicit-pmetas))) pmetas)))]
           [_ (unless (= (length named) (length (remove-dups named))) (oops "~a: repeated variable in ~s" f (cons f pats)))]
           [free (topo (filter (lambda (m) (not (meta-sol m))) (reverse pmetas)))]
           [c (fold-left (lambda (c m) (let ([c2 (bind c (meta-name m) (meta-type m))]) (solve! m (vvar (ctx-l c))) c2))
                         ctx0 free)]
           [c (fold-left (lambda (c m)
                           (if (or (memv m free) (eq? (meta-name m) '_)) c
                               (define-name c (meta-name m) (meta-val m) (meta-type m))))
                         c (reverse pmetas))]
           [t (zonked (ctx-l c) (ctx-env c) (check c body rest))])
      (k-check (ctx-env c) (ctx-tys c) (ctx-l c) t rest)
      (list (map (lambda (tr) (runtime-pat tr free)) trees) (ctx-l c) t))))

(define (remove-dups xs) (fold-right (lambda (x acc) (if (memq x acc) acc (cons x acc))) '() xs))

(define (topo ms)
  (define (deps m) (let walk ([t (reify 0 (meta-type m))])
                     (cond [(and (pair? t) (eq? (car t) 'meta)) (list (cadr t))]
                           [(pair? t) (apply append (map walk t))]
                           [else '()])))
  (let loop ([todo ms] [done '()])
    (if (null? todo) (reverse done)
        (let ([m (find (lambda (m) (for-all (lambda (d) (or (= d m) (memv d done) (not (memv d ms)))) (deps m))) todo)])
          (unless m (oops "circular dependencies between patterns"))
          (loop (remv m todo) (cons m done))))))

(define (runtime-pat tr free)
  (case (car tr)
    [(pmeta) (let ([i (index-of (cadr tr) free)]) (if i `(pvar ,i) '(pdot)))]
    [(pcon) `(pcon ,(cadr tr) ,(map (lambda (t) (runtime-pat t free)) (caddr tr)))]))

;; --- coverage: a candidate is split until every possible case is taken by a clause ---

(define fresh-count 0)
(define (fresh-sym) (set! fresh-count (+ fresh-count 1)) (string->symbol (format "?~a" fresh-count)))

;; A case as it would be written in a clause: [(right _) _ _]. Fresh variables are _.
(define (show-case f cand)                              ; the missing case as a call: (pick (right _) _ _)
  (define (pat p) (cond [(and (symbol? p) (char=? (string-ref (symbol->string p) 0) #\?)) '_]
                        [(and (pair? p) (null? (cdr p))) (pat (car p))]   ; (winter) is winter
                        [(pair? p) (map pat p)]
                        [else p]))
  (format "~s" (cons f (map pat cand))))

(define (cover f ty pats)
  (let loop ([todo (list (map (lambda (_) (fresh-sym)) (car pats)))])
    (unless (null? todo)
      (let ([cand (car todo)] [todo (cdr todo)])
        (set! pmetas '())
        (if (guard (x [(and (unify-failure? x) (eq? (unify-failure-kind x) 'conflict)) #f]
                      [(unify-failure? x) (oops "~a: cannot decide whether the case ~a is possible" f (show-case f cand))])
              (call-with-values (lambda () (check-pats ty cand)) (lambda _ #t)))
            (let ([r (exists (lambda (q) (let ([r (match-syn* q cand)]) (and (not (eq? r 'no)) r))) pats)])
              (cond [(and (not r) (empty-split? f ty cand)) (loop todo)]
                    [(not r) (oops "~a: missing case ~a" f (show-case f cand))]
                    [(eq? r 'yes) (loop todo)]
                    [else (loop (append (split f r cand) todo))]))
            (loop todo))))))                            ; impossible case: the indices do not unify

;; A case no clause takes is covered anyway if one of its variables, split by constructors,
;; gives only impossible cases: that variable's type is empty (the implicit ()).
(define (empty-split? f ty cand)
  (define (vars t) (cond [(and (symbol? t) (char=? (string-ref (symbol->string t) 0) #\?)) (list t)]
                         [(pair? t) (apply append (map vars t))]
                         [else '()]))
  (define (impossible? c)
    (set! pmetas '())
    (guard (e [(and (unify-failure? e) (eq? (unify-failure-kind e) 'conflict)) #t] [(unify-failure? e) #f])
      (call-with-values (lambda () (check-pats ty c)) (lambda _ #f))))
  (exists (lambda (x)
            (set! pmetas '())
            (call-with-values (lambda () (check-pats ty cand)) (lambda _ #t))
            (let* ([m (find (lambda (m) (eq? (meta-name m) x)) pmetas)] [t (and m (force (meta-type m)))])
              (and t (eq? (car t) 'vglob) (eq? (g-kind (gget (cadr t))) 'data)
                   (for-all impossible? (split f x cand)))))
          (vars cand)))

(define (match-syn q c)                                 ; → yes | no | the candidate's variable to split
  (cond [(or (symbol? q) (null? q)) 'yes]                ; () covers: the position is empty (verified)
        [(symbol? c) c]
        [(not (eq? (car q) (car c))) 'no]
        [else (match-syn* (cdr q) (cdr c))]))
(define (match-syn* qs cs)
  (let ([rs (map match-syn qs cs)])
    (cond [(memq 'no rs) 'no]
          [(find (lambda (r) (not (eq? r 'yes))) rs) => values]
          [else 'yes])))

(define (split f x cand)
  (let ([ty (force (meta-type (find (lambda (m) (eq? (meta-name m) x)) pmetas)))])
    (unless (and (eq? (car ty) 'vglob) (eq? (g-kind (gget (cadr ty))) 'data)) (oops "~a: cannot split ~a" f x))
    (map (lambda (k)
           (let ([new (cons k (map (lambda (_) (fresh-sym)) (explicit-args k)))])
             (let subst ([t cand]) (cond [(eq? t x) new] [(pair? t) (map subst t)] [else t]))))
         (g-info (gget (cadr ty))))))

(define (explicit-args k)
  (let loop ([t (force (g-type (gget k)))] [l 0] [acc '()])
    (if (eq? (car t) 'vpi)
        (loop (force (pi-cod t (vvar l))) (+ l 1) (if (eq? (caddr t) 'e) (cons l acc) acc))
        acc)))

;; --- termination: in every recursive call a fixed argument is a strict subterm ---
;; ponytail: a single decreasing argument, no lexicographic order; add it if needed.

(define (terminates! f cs)
  (define (calls t d)                                   ; → list of (arguments . depth)
    (let-values ([(h args) (spine-of t)])
      (append (if (equal? h `(glob ,f)) (list (cons args d)) '())
              (case (car h)
                [(lam) (calls (cadddr h) (+ d 1))]
                [(pi) (append (calls (cadddr h) d) (calls (list-ref h 4) (+ d 1)))]
                [(ann) (append (calls (cadr h) d) (calls (caddr h) d))]   ; also inside a the
                [(at) (calls (caddr h) d)]
                [else '()])
              (apply append (map (lambda (a) (calls a d)) args)))))
  (define (inside? l p) (or (equal? p `(pvar ,l)) (and (eq? (car p) 'pcon) (exists (lambda (q) (inside? l q)) (caddr p)))))
  (define (decreases? call i c)
    (let ([args (car call)])
      (and (> (length args) i)
           (let ([a (list-ref args i)] [p (list-ref (car c) i)])
             (and (eq? (car a) 'var) (eq? (car p) 'pcon)
                  (exists (lambda (q) (inside? (- (cdr call) (cadr a) 1) q)) (caddr p)))))))
  (let ([all (map (lambda (c) (calls (caddr c) (cadr c))) cs)])
    (unless (or (for-all null? all)
                (exists (lambda (i) (for-all (lambda (c cl) (for-all (lambda (call) (decreases? call i c)) cl)) cs all))
                        (iota (length (car (car cs))))))
      (oops "~a: recursion is not structural" f))))

;; --- printing for error messages ---

(define (show c v) (sexp (ctx-names c) (reify (ctx-l c) v)))

;; TODO, as in Pie: a hole in a define's body. The checker collects the goal and context of
;; every hole of the define and rejects it with them: a hole is never a postulate. The
;; message is written at the end, when unification has solved what it could.
(define todos (make-parameter #f))                        ; box with the current define's holes
(define (todo! c ty)
  (unless (todos) (oops "TODO goes in the body of a define"))
  (let ([p (here)])
    (set-box! (todos) (cons (lambda () (todo-message p c ty)) (unbox (todos))))
    `(imeta ,(new-meta 'TODO #f))))
(define (todo-message p c ty)
  (let* ([l (ctx-l c)] [names (ctx-names c)]
         [hyps (filter values
                 (map (lambda (i)
                        (let ([x (list-ref names i)])
                          (and (symbol? x) (not (char=? (string-ref (symbol->string x) 0) #\%))
                               (format "  ~a : ~s" x (sexp (list-tail names (+ i 1)) (reify (- l i 1) (list-ref (ctx-tys c) i)))))))
                      (reverse (iota l))))]
         [defs (map (lambda (d) (format "  ~a = ~s : ~s" (car d) (show c (cadr d)) (show c (caddr d)))) (reverse (ctx-defs c)))])
    (format "~@[~a: ~]TODO~{\n~a~}\n  ──────────\n  ~s" (and p (pos->string p)) (append hyps defs) (show c ty))))
(define (flush-todos!)
  (let ([ms (if (todos) (map (lambda (k) (k)) (reverse (unbox (todos)))) '())])
    (unless (null? ms) (error 'disegno (fold-left (lambda (acc m) (string-append acc "\n" m)) (car ms) (cdr ms))))))
(define (sexp names t)
  (cond [(and (equal? (car t) 'app) (bi 'obj) (equal? (cadr t) `(glob ,(bi 'obj))) (equal? (car (caddr t)) 'glob))
         (kind-alias (cadr (caddr t)))]                  ; (Obj Kind.cache-volume) reads CacheVolume
        [(literal-of t) => values]                       ; points and segments as written: /out/bin, "bin"
        [else (sexp1 names t)]))

;; Refined values printed as written: (image "alpine" tt) → "alpine", (port 8080 tt) →
;; 8080: a constructor with a literal and then proofs only. Addresses have their own form:
;; (ip n tt) → "10.0.0.5", (cidr 2561 24 tt) → "10.0.1.0/24".
(define (refined t)
  (let-values ([(h args) (spine-of t)])
    (define (num i) (and (> (length args) i) (eq? (car (list-ref args i)) 'num) (cadr (list-ref args i))))
    (define (proofs? as) (for-all (lambda (a) (equal? a `(glob ,(bi 'tt)))) as))
    (let ([k (and (eq? (car h) 'glob) (con? (cadr h)) (hashtable-ref builtin-of (g-info (gget (cadr h))) #f))])
      (cond [(and (eq? k 'cidr) (num 0) (num 1)) (format "~a/~a" (nat->ip (* (num 0) (expt 2 (- 32 (num 1))))) (num 1))]
            [(and (eq? k 'ip) (num 0)) (nat->ip (num 0))]
            [(and (eq? (car h) 'glob) (con? (cadr h)) (pair? args) (pair? (cdr args)) (memq (car (car args)) '(str num))
                  (proofs? (cdr args)))
             (cadr (car args))]
            [else #f]))))

(define (literal-of t)
  (define (seg t)                                        ; (segment "x" proof) → "x"
    (let-values ([(h args) (spine-of t)])
      (and (eq? (car h) 'glob) (con? (cadr h)) (bi? (g-info (gget (cadr h))) 'segment)
           (pair? args) (eq? (car (car args)) 'str) (cadr (car args)))))
  (define (abs t)                                        ; → list of segments, or #f
    (let-values ([(h args) (spine-of t)])
      (cond [(and (bi 'root) (equal? t `(glob ,(bi 'root)))) '()]
            [(and (bi 'slash) (equal? h `(glob ,(bi 'slash))) (= (length args) 2))
             (let ([p (abs (car args))] [s (seg (cadr args))]) (and p s (append p (list s))))]
            [else #f])))
  (define (rel t)                                        ; (step (step here "bin") "hello") → ("bin" "hello")
    (let-values ([(h args) (spine-of t)])
      (cond [(and (bi 'here) (equal? t `(glob ,(bi 'here)))) '()]
            [(and (bi 'step) (equal? h `(glob ,(bi 'step))) (= (length args) 2))
             (let ([p (rel (car args))] [s (seg (cadr args))]) (and p s (append p (list s))))]
            [else #f])))
  (cond [(abs t) => (lambda (ss) (string->symbol (apply string-append "/" (let loop ([ss ss]) (if (or (null? ss) (null? (cdr ss))) ss (cons* (car ss) "/" (loop (cdr ss))))))))]
        [(seg t) => values]
        [(refined t) => values]
        [(rel t) => (lambda (ss) (if (null? ss) "" (fold-left (lambda (a s) (string-append a "/" s)) (car ss) (cdr ss))))]
        [else #f]))

(define (kind-alias k)
  (case k
    [(Kind.bool) '(Remote Bool)]                          ; an observation, not a Bool
    [(Kind.export) '(Export Dir)]                          ; ponytail: printing only, the names of dagger.disegno
    [else (kind-alias1 k)]))

(define (kind-alias1 k)
  (let ([s (symbol->string k)])
    (string->symbol
      (let loop ([cs (string->list (substring s 5 (string-length s)))] [up #t])
        (cond [(null? cs) ""]
              [(char=? (car cs) #\-) (loop (cdr cs) #t)]
              [else (string-append (string (if up (char-upcase (car cs)) (car cs))) (loop (cdr cs) #f))])))))

(define (sexp1 names t)
  (case (car t)
    [(var) (if (< (cadr t) (length names)) (list-ref names (cadr t)) t)]
    [(glob) (cadr t)]
    [(str) (cadr t)]
    [(num) (cadr t)]
    [(ann) `(the ,(sexp names (caddr t)) ,(sexp names (cadr t)))]
    [(at) (sexp names (caddr t))]
    [(type) (if (zero? (cadr t)) 'Type `(Type ,(cadr t)))]
    [(meta imeta) (string->symbol (format "?~a" (cadr t)))]
    [(lam) `(λ ,(cadr t) ,(sexp (cons (cadr t) names) (cadddr t)))]
    [(pi) (if (eq? (cadr t) '_) `(→ ,(sexp names (cadddr t)) ,(sexp (cons (cadr t) names) (list-ref t 4)))
              `(Π ((,(cadr t) ,(sexp names (cadddr t)))) ,(sexp (cons (cadr t) names) (list-ref t 4))))]
    [(app) (let loop ([t t] [as '()])               ; shows only the explicit arguments
             (cond [(not (eq? (car t) 'app)) (if (null? as) (sexp names t) (cons (sexp names t) as))]
                   [(eq? (cadddr t) 'e) (loop (cadr t) (cons (sexp names (caddr t)) as))]
                   [else (loop (cadr t) as)]))]))

;; --- readable types, as written: (∀ ((A Type)) (Π ((x A)) (→ B C))) ---
;; Nested arrows are flattened; a binder without a name is just its type; adjacent binders of
;; the same kind share one Π (explicit) or ∀ (implicit). For the LSP's hover and for
;; disegno type.

(define (render-term names t)
  (if (eq? (car t) 'pi)
      (let loop ([names names] [t t] [parts '()])        ; parts: (kind name domain), kind ∈ Π ∀ →
        (if (eq? (car t) 'pi)
            (let* ([x (let ([s (symbol->string (cadr t))])   ; %r (internal) shows as r
                        (if (and (> (string-length s) 1) (char=? (string-ref s 0) #\%)) (substring s 1 (string-length s)) s))]
                   [dom (render-term names (cadddr t))]
                   [kind (cond [(eq? (caddr t) 'i) '∀] [(string=? x "_") '→] [else 'Π])])
              (loop (cons (cadr t) names) (list-ref t 4) (cons (list kind x dom) parts)))
            (let render ([ps (reverse parts)])
              (if (null? ps)
                  (render-term names t)
                  (let* ([k (car (car ps))]
                         [run (let take ([ps ps]) (if (and (pair? ps) (eq? (car (car ps)) k)) (cons (car ps) (take (cdr ps))) '()))]
                         [rest (list-tail ps (length run))])
                    (if (eq? k '→)
                        (format "(→ ~{~a ~}~a)" (map caddr run) (render rest))
                        (format "(~a (~{~a~^ ~}) ~a)" k (map (lambda (p) (format "(~a ~a)" (cadr p) (caddr p))) run) (render rest))))))))
      (let ([s (sexp names t)])
        (call-with-string-output-port (lambda (p) (write s p))))))

(define (type-of-global name)                            ; → "name : type", or #f
  (let ([g (gget name)])
    (and g (format "~a : ~a" name (render-term '() (reify 0 (g-type g)))))))
