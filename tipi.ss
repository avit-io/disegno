;; Type checker di Disegno.
;; Elaboratore (non fidato): nomi, argomenti impliciti, metavariabili, pattern.
;; Kernel (fidato): ricontrolla ogni termine elaborato, con universi stratificati.
;; Stile elaboration-zoo (Kovács): termini con indici di de Bruijn, valori con livelli, NbE.
;;
;; Termini: (var i) (glob n) (app f u i) (lam x i b) (pi x i a b) (type n) (meta m) (imeta m)
;; Valori:  (vlam x i env b) (vpi x i a env b) (vtype n) (vrigid l sp) (vflex m sp) (vglob n sp)
;; Visibilità i ∈ {e, i}. Spine: lista di (valore . visibilità) in ordine di applicazione.

(define (oops fmt . args) (error 'disegno (apply format fmt args)))

;; --- globali e metavariabili ---

(define-record-type g (fields kind type (mutable info)))  ; data: costruttori; con: data; def: (arità . clausole)
(define globals (make-eq-hashtable))
(define (gget n) (and (symbol? n) (hashtable-ref globals n #f)))
(define (con? n) (let ([g (gget n)]) (and g (eq? (g-kind g) 'con))))
(define (fresh-name! n) (when (gget n) (oops "~a è già definito" n)))

(define metas (make-eqv-hashtable))                     ; m → #(soluzione nome tipo)
(define (new-meta name type)
  (let ([m (+ 1 (hashtable-size metas))]) (hashtable-set! metas m (vector #f name type)) m))
(define (meta-sol m) (vector-ref (hashtable-ref metas m #f) 0))
(define (meta-name m) (vector-ref (hashtable-ref metas m #f) 1))
(define (meta-type m) (vector-ref (hashtable-ref metas m #f) 2))
(define (solve! m v) (vector-set! (hashtable-ref metas m #f) 0 v))
(define (meta-val m) (or (meta-sol m) `(vflex ,m ())))

(define pmetas '())                                     ; variabili di pattern della clausola corrente
(define (new-pmeta name type) (let ([m (new-meta name type)]) (set! pmetas (cons m pmetas)) m))

;; --- valutazione ---

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
    [(meta) (meta-val (cadr t))]
    [(imeta) (fold-left (lambda (f v) (vapp f v 'e)) (meta-val (cadr t)) (reverse env))]))

(define (vapp f u i)
  (let ([a (list (cons u i))])
    (case (car f)
      [(vlam) (ev (cons u (cadddr f)) (list-ref f 4))]
      [(vflex vrigid) `(,(car f) ,(cadr f) ,(append (caddr f) a))]
      [(vglob) (reduce (cadr f) (append (caddr f) a))]
      [else (ufail 'mismatch)])))
(define (vapp-sp f sp) (fold-left (lambda (f a) (vapp f (car a) (cdr a))) f sp))

(define (force v)
  (case (car v)
    [(vflex) (let ([s (meta-sol (cadr v))]) (if s (force (vapp-sp s (caddr v))) v))]
    [(vglob) (let ([r (try-reduce (cadr v) (caddr v))]) (if r (force r) v))]
    [else v]))

;; Una def si riduce quando ha tutti gli argomenti e una clausola combacia; altrimenti resta bloccata.
(define (reduce n sp) (or (try-reduce n sp) `(vglob ,n ,sp)))
(define (try-reduce n sp)
  (let* ([g (gget n)] [info (and (eq? (g-kind g) 'def) (g-info g))])
    (and info (>= (length sp) (car info))
         (let ([r (match-clauses (cdr info) (list-head sp (car info)))])
           (and r (vapp-sp r (list-tail sp (car info))))))))

;; Clausola a runtime: (pattern n corpo); pattern: (pvar livello) (pdot) (pcon c pattern...).
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
              (cond [(not (and (eq? (car v) 'vglob) (con? (cadr v)))) 'stuck]
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
      [(vtype) `(type ,(cadr v))])))

;; --- unificazione (senza metavariabili è la conversione del kernel) ---

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
      [(and (is? a 'vrigid) (is? b 'vrigid) (= (cadr a) (cadr b))) (unify-sp l (caddr a) (caddr b))]
      [(and (is? a 'vglob) (is? b 'vglob))
       (cond [(eq? (cadr a) (cadr b)) (unify-sp l (caddr a) (caddr b))]
             [(and (con? (cadr a)) (con? (cadr b))) (ufail 'conflict)]
             [else (ufail 'mismatch)])]
      [(and (is? a 'vflex) (is? b 'vflex) (= (cadr a) (cadr b))) (unify-sp l (caddr a) (caddr b))]
      ;; flex-flex: si risolve la meta col contesto più grande, così l'altra resta nel suo scope
      [(and (is? a 'vflex) (is? b 'vflex) (< (length (caddr a)) (length (caddr b)))) (solve l (cadr b) (caddr b) a)]
      [(is? a 'vflex) (solve l (cadr a) (caddr a) b)]
      [(is? b 'vflex) (solve l (cadr b) (caddr b) a)]
      [else (ufail 'mismatch)])))

(define (unify-sp l s1 s2)
  (unless (= (length s1) (length s2)) (ufail 'mismatch))
  (for-each (lambda (x y) (unify l (car x) (car y))) s1 s2))

;; Unificazione a pattern di Miller: ?m x1..xn = rhs, con xi variabili distinte.
(define (solve l m sp rhs)
  (let ([t (rename-v m (length sp) l (invert sp) rhs)])
    (solve! m (ev '() (fold-right (lambda (a t) `(lam x ,(cdr a) ,t)) t sp)))))

(define (invert sp)                                     ; livello nel contesto → livello nella soluzione
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
      [(vtype) `(type ,(cadr v))])))

;; --- kernel: l'unica parte fidata del controllo ---

(define (k-infer env tys l t)
  (case (car t)
    [(var) (list-ref tys (cadr t))]
    [(glob) (let ([g (gget (cadr t))]) (if g (g-type g) (oops "kernel: ~a non esiste" (cadr t))))]
    [(type) `(vtype ,(+ (cadr t) 1))]                   ; Type n : Type n+1, mai Type : Type
    [(pi) (let ([la (k-level (k-infer env tys l (cadddr t)))])
            `(vtype ,(max la (k-level (k-infer (cons (vvar l) env) (cons (ev env (cadddr t)) tys) (+ l 1) (list-ref t 4))))))]
    [(app) (let ([tf (force (k-infer env tys l (cadr t)))])
             (unless (and (eq? (car tf) 'vpi) (eq? (caddr tf) (cadddr t))) (oops "kernel: applicazione mal tipata"))
             (k-check env tys l (caddr t) (pi-dom tf))
             (pi-cod tf (ev env (caddr t))))]
    [else (oops "kernel: termine non inferibile ~s" t)]))

(define (k-check env tys l t ty)
  (let ([ty (force ty)])
    (if (and (eq? (car t) 'lam) (eq? (car ty) 'vpi) (eq? (caddr t) (caddr ty)))
        (k-check (cons (vvar l) env) (cons (pi-dom ty) tys) (+ l 1) (cadddr t) (pi-cod ty (vvar l)))
        (guard (x [(unify-failure? x) (oops "kernel: tipo errato")])
          (unify l (k-infer env tys l t) ty)))))

(define (k-level ty)
  (let ([ty (force ty)]) (if (eq? (car ty) 'vtype) (cadr ty) (oops "kernel: atteso un tipo"))))
(define (k-type t) (k-level (k-infer '() '() 0 t)))

;; --- elaboratore ---

(define-record-type ctx (fields l env tys names defs))  ; defs: variabili di pattern forzate, (nome valore tipo)
(define ctx0 (make-ctx 0 '() '() '() '()))
(define (bind c x ty)
  (make-ctx (+ 1 (ctx-l c)) (cons (vvar (ctx-l c)) (ctx-env c)) (cons ty (ctx-tys c)) (cons x (ctx-names c)) (ctx-defs c)))
(define (define-name c x v ty)
  (make-ctx (ctx-l c) (ctx-env c) (ctx-tys c) (ctx-names c) (cons (list x v ty) (ctx-defs c))))

(define (index-of x xs)
  (let loop ([xs xs] [i 0]) (cond [(null? xs) #f] [(equal? (car xs) x) i] [else (loop (cdr xs) (+ i 1))])))
(define (nat? e) (and (integer? e) (exact? e) (>= e 0)))
(define (nat n) (if (zero? n) '(glob zero) `(app (glob add1) ,(nat (- n 1)) e)))

;; ponytail: il reader di Chez legge [..] come (..), quindi in (→ ...) un binder è (x T) con x non globale.
(define (binder? e)
  (and (list? e) (= (length e) 2) (symbol? (car e)) (not (eq? (car e) 'Type)) (not (gget (car e)))))

(define (infer c e)                                     ; → (values termine tipo)
  (cond
    [(eq? e 'Type) (values '(type 0) '(vtype 1))]
    [(eq? e '_) (oops "_ non è un termine")]
    [(nat? e) (unless (gget 'Nat) (oops "i letterali richiedono Nat")) (values (nat e) '(vglob Nat ()))]
    [(symbol? e)
     (cond [(index-of e (ctx-names c)) => (lambda (i) (values `(var ,i) (list-ref (ctx-tys c) i)))]
           [(assq e (ctx-defs c)) => (lambda (d) (values (reify (ctx-l c) (cadr d)) (caddr d)))]
           [(gget e) => (lambda (g) (values `(glob ,e) (g-type g)))]
           [else (oops "nome sconosciuto: ~a" e)])]
    [(and (pair? e) (eq? (car e) '→))
     (let-values ([(t n) (elab-arrow c (cdr e))]) (values t `(vtype ,n)))]
    [(and (pair? e) (eq? (car e) 'Type) (nat? (cadr e))) (values `(type ,(cadr e)) `(vtype ,(+ 1 (cadr e))))]
    [(pair? e)
     (let-values ([(t ty) (infer c (car e))])
       (let loop ([t t] [ty ty] [args (cdr e)])
         (if (null? args) (values t ty)
             (let-values ([(t ty) (insert c t ty)])
               (unless (and (eq? (car ty) 'vpi) (eq? (caddr ty) 'e)) (oops "troppi argomenti in ~s" e))
               (let ([u (check c (car args) (pi-dom ty))])
                 (loop `(app ,t ,u e) (pi-cod ty (ev (ctx-env c) u)) (cdr args)))))))]
    [else (oops "espressione non valida: ~s" e)]))

(define (insert c t ty)                                 ; applica gli impliciti in testa con metavariabili
  (let ([ty (force ty)])
    (if (and (eq? (car ty) 'vpi) (eq? (caddr ty) 'i))
        (let ([m `(imeta ,(new-meta #f #f))])
          (insert c `(app ,t ,m i) (pi-cod ty (ev (ctx-env c) m))))
        (values t ty))))

(define (check c e ty)
  (let*-values ([(t ty2) (infer c e)] [(t ty2) (insert c t ty2)])
    (guard (x [(unify-failure? x) (oops "~s: atteso ~s, trovato ~s" e (show c ty) (show c ty2))])
      (unify (ctx-l c) ty2 ty))
    t))

(define (check-type c e)                                ; → (values termine livello)
  (let-values ([(t ty) (infer c e)])
    (let ([ty (force ty)])
      (case (car ty)
        [(vtype) (values t (cadr ty))]
        [(vflex) (unify (ctx-l c) ty '(vtype 0)) (values t 0)]  ; ponytail: tipo ignoto ⇒ Type₀, niente polimorfismo di universo
        [else (oops "~s non è un tipo" e)]))))

(define (elab-arrow c as)                               ; → (values termine livello)
  (if (null? (cdr as))
      (check-type c (car as))
      (let*-values ([(x a) (if (binder? (car as)) (values (caar as) (cadar as)) (values '_ (car as)))]
                    [(ta na) (check-type c a)]
                    [(tb nb) (elab-arrow (bind c x (ev (ctx-env c) ta)) (cdr as))])
        (values `(pi ,x e ,ta ,tb) (max na nb)))))

;; Variabili libere di una firma, in ordine di prima occorrenza: diventano argomenti impliciti.
(define (free-vars e)
  (let ([acc '()])
    (let walk ([e e] [bound '()])
      (cond
        [(symbol? e)
         (unless (or (memq e bound) (memq e acc) (gget e) (memq e '(→ Type _))) (set! acc (cons e acc)))]
        [(and (pair? e) (eq? (car e) '→))
         (let loop ([as (cdr e)] [bound bound])
           (cond [(null? as) (void)]
                 [(and (pair? (cdr as)) (binder? (car as)))
                  (walk (cadar as) bound) (loop (cdr as) (cons (caar as) bound))]
                 [else (walk (car as) bound) (loop (cdr as) bound)]))]
        [(pair? e) (for-each (lambda (x) (walk x bound)) e)]))
    (reverse acc)))

;; Firma → termine chiuso. Se il tipo di una variabile libera resta ignoto lo si generalizza:
;; (≡ x x) diventa {x:tipo : Type}{x : x:tipo} → ≡ x x.
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
          (retry (append gen (map (lambda (p) (cons (car p) (string->symbol (format "~a:tipo" (car p))))) open)))))))

(define (zonk l env t)                                  ; sostituisce le metavariabili risolte
  (case (car t)
    [(meta imeta) (reify l (ev env t))]
    [(app) `(app ,(zonk l env (cadr t)) ,(zonk l env (caddr t)) ,(cadddr t))]
    [(lam) `(lam ,(cadr t) ,(caddr t) ,(zonk (+ l 1) (cons (vvar l) env) (cadddr t)))]
    [(pi) `(pi ,(cadr t) ,(caddr t) ,(zonk l env (cadddr t)) ,(zonk (+ l 1) (cons (vvar l) env) (list-ref t 4)))]
    [else t]))
(define (zonked l env t)
  (let ([z (zonk l env t)])
    (when (let has? ([z z]) (and (pair? z) (or (memq (car z) '(meta imeta)) (exists has? z))))
      (oops "impossibile inferire gli argomenti impliciti in ~s" (sexp '() z)))
    z))

;; --- dichiarazioni ---

(define (check-decl d)
  (case (and (pair? d) (car d))
    [(data) (check-data d)]
    [(def) (check-def d)]
    [else (oops "dichiarazione sconosciuta: ~s" d)]))

(define (check-port p)
  (let loop () (let ([d (read p)]) (unless (eof-object? d) (check-decl d) (loop)))))
(define (check-file path)
  (call-with-port (open-file-input-port path (file-options) (buffer-mode block) (make-transcoder (utf-8-codec)))
    check-port))
(define (check-string s) (check-port (open-string-input-port s)))

;; (data Nat [zero] [add1 Nat])  oppure  (data Vec : (→ Type Nat Type) [nil : (Vec A 0)] ...)
(define (check-data d)
  (let*-values ([(name) (cadr d)]
                [(sig ks) (if (and (pair? (cddr d)) (eq? (caddr d) ':))
                              (values (cadddr d) (map (lambda (k) (cons (car k) (caddr k))) (list-tail d 4)))
                              (values 'Type (map (lambda (k) (cons (car k) (if (null? (cdr k)) name `(→ ,@(cdr k) ,name))))
                                                 (cddr d))))])
    (fresh-name! name)
    (let* ([t (elab-sig sig)] [n (begin (k-type t) (data-level (ev '() t)))])
      (hashtable-set! globals name (make-g 'data (ev '() t) '()))
      (let* ([cts (map (lambda (k) (fresh-name! (car k)) (elab-sig (cdr k))) ks)]
             [teles (map (lambda (k ct) (telescope name (car k) ct)) ks cts)]
             [params (param-positions teles)])
        (for-each (lambda (k tele) (check-con name n params (car k) tele)) ks teles)
        (for-each (lambda (k ct) (hashtable-set! globals (car k) (make-g 'con (ev '() ct) name))) ks cts)
        (g-info-set! (gget name) (map car ks))))))

(define (data-level v)
  (let loop ([v (force v)] [l 0])
    (case (car v)
      [(vpi) (loop (force (pi-cod v (vvar l))) (+ l 1))]
      [(vtype) (cadr v)]
      [else (oops "il tipo di un data deve finire in Type")])))

;; → (binder . spine del tipo di ritorno); binder = (visibilità livello dominio-normalizzato)
(define (telescope d k t)
  (k-type t)
  (let loop ([env '()] [tys '()] [l 0] [t t] [bs '()])
    (if (eq? (car t) 'pi)
        (let ([va (ev env (cadddr t))])
          (loop (cons (vvar l) env) (cons va tys) (+ l 1) (list-ref t 4)
                (cons (list (caddr t) (k-level (k-infer env tys l (cadddr t))) (reify l va)) bs)))
        (let ([r (force (ev env t))])
          (unless (and (eq? (car r) 'vglob) (eq? (cadr r) d)) (oops "il costruttore ~a deve restituire ~a" k d))
          (cons (reverse bs) (caddr r))))))

;; Parametro: posizione occupata in ogni costruttore da una variabile implicita nuda (A in Vec A n).
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
          (oops "~a: un campo di livello ~a non sta in ~a, di livello ~a" k (cadr (car bs)) d n))
        (unless (strictly-positive? d (caddr (car bs)))
          (oops "~a: ~a non compare in posizione strettamente positiva" k d))
        (loop (cdr bs) (+ l 1))))
    (for-each (lambda (a) (when (mentions? d (reify (length (car tele)) (car a))) (oops "~a: ~a negli indici di sé stesso" k d)))
              (cdr tele))))

(define (mentions? d t) (or (equal? t `(glob ,d)) (and (pair? t) (exists (lambda (x) (mentions? d x)) t))))
(define (spine-of t)
  (let loop ([t t] [args '()]) (if (eq? (car t) 'app) (loop (cadr t) (cons (caddr t) args)) (values t args))))
(define (strictly-positive? d t)
  (or (not (mentions? d t))
      (and (eq? (car t) 'pi) (not (mentions? d (cadddr t))) (strictly-positive? d (list-ref t 4)))
      (let-values ([(h args) (spine-of t)])
        (and (equal? h `(glob ,d)) (not (exists (lambda (a) (mentions? d a)) args))))))

;; (def f : T [p ...] corpo ...)  oppure  (def f : T corpo)
(define (check-def d)
  (unless (and (>= (length d) 4) (eq? (caddr d) ':)) (oops "def malformata: ~s" d))
  (let* ([name (cadr d)] [rest (list-tail d 4)]
         [clauses (cond [(null? rest) (oops "~a: manca la definizione" name)]
                        [(null? (cdr rest)) (list (cons '() (car rest)))]
                        [(odd? (length rest)) (oops "~a: clausola senza corpo" name)]
                        [else (let pairs ([r rest]) (if (null? r) '() (cons (cons (car r) (cadr r)) (pairs (cddr r)))))])])
    (fresh-name! name)
    (let* ([t (elab-sig (cadddr d))] [ty (begin (k-type t) (ev '() t))])
      (hashtable-set! globals name (make-g 'def ty #f))
      (let* ([pats (map (lambda (c) (map norm-pat (car c))) clauses)]
             [_ (unless (apply = (map length pats)) (oops "~a: le clausole hanno numeri di pattern diversi" name))]
             [cs (map (lambda (ps c) (check-clause name ty ps (cdr c))) pats clauses)])
        (cover name ty pats)
        (terminates! name cs)
        (g-info-set! (gget name) (cons (length (car (car cs))) cs))))))

(define (norm-pat p)
  (cond [(nat? p) (if (zero? p) '(zero) `(add1 ,(norm-pat (- p 1))))]
        [(con? p) (list p)]
        [(symbol? p) p]
        [(and (pair? p) (con? (car p))) (cons (car p) (map norm-pat (cdr p)))]
        [else (oops "pattern non valido: ~s" p)]))

;; Fase A: i pattern si controllano con le variabili come metavariabili chiuse, così
;; l'unificazione degli indici le risolve (pattern forzati). → (values alberi tipo-restante)
(define (check-pats ty pats)
  (let loop ([ty ty] [pats pats] [trees '()])
    (if (null? pats)
        (values (reverse trees) ty)
        (let ([ty (force ty)])
          (unless (eq? (car ty) 'vpi) (oops "troppi pattern"))
          (if (eq? (caddr ty) 'i)
              (let ([m (new-pmeta '_ (pi-dom ty))]) (loop (pi-cod ty (meta-val m)) pats (cons `(pmeta ,m) trees)))
              (let-values ([(tree v) (check-pat (car pats) (pi-dom ty))])
                (loop (pi-cod ty v) (cdr pats) (cons tree trees))))))))

(define (check-pat p ty)                                ; → (values albero valore)
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
            [(or (eq? (car kty) 'vpi) (pair? ps)) (oops "numero di argomenti sbagliato in ~s" p)]
            [else (unify 0 kty ty)
                  (values `(pcon ,(car p) ,(reverse trees)) `(vglob ,(car p) ,(reverse sp)))])))))

;; Fase B: le variabili non risolte diventano il contesto (in ordine di dipendenza),
;; quelle risolte diventano nomi definiti. Poi corpo: elaborato, zonkato, ricontrollato dal kernel.
(define (check-clause f ty pats body)
  (set! pmetas '())
  (let-values ([(trees rest) (guard (x [(unify-failure? x) (oops "~a: clausola ~s impossibile o mal tipata" f pats)])
                               (check-pats ty pats))])
    (let* ([named (filter (lambda (x) (not (eq? x '_))) (map meta-name pmetas))]
           [_ (unless (= (length named) (length (remove-dups named))) (oops "~a: variabile ripetuta in ~s" f pats))]
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
          (unless m (oops "dipendenze circolari tra i pattern"))
          (loop (remv m todo) (cons m done))))))

(define (runtime-pat tr free)
  (case (car tr)
    [(pmeta) (let ([i (index-of (cadr tr) free)]) (if i `(pvar ,i) '(pdot)))]
    [(pcon) `(pcon ,(cadr tr) ,(map (lambda (t) (runtime-pat t free)) (caddr tr)))]))

;; --- copertura: si divide un candidato finché ogni caso possibile è preso da una clausola ---

(define fresh-count 0)
(define (fresh-sym) (set! fresh-count (+ fresh-count 1)) (string->symbol (format "?~a" fresh-count)))

(define (cover f ty pats)
  (let loop ([todo (list (map (lambda (_) (fresh-sym)) (car pats)))])
    (unless (null? todo)
      (let ([cand (car todo)] [todo (cdr todo)])
        (set! pmetas '())
        (if (guard (x [(and (unify-failure? x) (eq? (unify-failure-kind x) 'conflict)) #f]
                      [(unify-failure? x) (oops "~a: non so decidere se il caso ~s è possibile" f cand)])
              (call-with-values (lambda () (check-pats ty cand)) (lambda _ #t)))
            (let ([r (exists (lambda (q) (let ([r (match-syn* q cand)]) (and (not (eq? r 'no)) r))) pats)])
              (cond [(not r) (oops "~a: manca il caso ~s" f cand)]
                    [(eq? r 'yes) (loop todo)]
                    [else (loop (append (split f r cand) todo))]))
            (loop todo))))))                            ; caso impossibile: gli indici non si unificano

(define (match-syn q c)                                 ; → yes | no | variabile del candidato da dividere
  (cond [(symbol? q) 'yes]
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
    (unless (and (eq? (car ty) 'vglob) (eq? (g-kind (gget (cadr ty))) 'data)) (oops "~a: non posso dividere ~a" f x))
    (map (lambda (k)
           (let ([new (cons k (map (lambda (_) (fresh-sym)) (explicit-args k)))])
             (let subst ([t cand]) (cond [(eq? t x) new] [(pair? t) (map subst t)] [else t]))))
         (g-info (gget (cadr ty))))))

(define (explicit-args k)
  (let loop ([t (force (g-type (gget k)))] [l 0] [acc '()])
    (if (eq? (car t) 'vpi)
        (loop (force (pi-cod t (vvar l))) (+ l 1) (if (eq? (caddr t) 'e) (cons l acc) acc))
        acc)))

;; --- terminazione: in ogni chiamata ricorsiva un argomento fisso è un sottotermine stretto ---
;; ponytail: un solo argomento decrescente, niente ordine lessicografico; aggiungerlo se serve.

(define (terminates! f cs)
  (define (calls t d)                                   ; → lista di (argomenti . profondità)
    (let-values ([(h args) (spine-of t)])
      (append (if (equal? h `(glob ,f)) (list (cons args d)) '())
              (case (car h)
                [(lam) (calls (cadddr h) (+ d 1))]
                [(pi) (append (calls (cadddr h) d) (calls (list-ref h 4) (+ d 1)))]
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
      (oops "~a: ricorsione non strutturale" f))))

;; --- stampa per i messaggi d'errore ---

(define (show c v) (sexp (ctx-names c) (reify (ctx-l c) v)))
(define (sexp names t)
  (case (car t)
    [(var) (if (< (cadr t) (length names)) (list-ref names (cadr t)) t)]
    [(glob) (cadr t)]
    [(type) (if (zero? (cadr t)) 'Type `(Type ,(cadr t)))]
    [(meta imeta) (string->symbol (format "?~a" (cadr t)))]
    [(lam) `(λ ,(cadr t) ,(sexp (cons (cadr t) names) (cadddr t)))]
    [(pi) `(→ (,(cadr t) ,(sexp names (cadddr t))) ,(sexp (cons (cadr t) names) (list-ref t 4)))]
    [(app) (let loop ([t t] [as '()])               ; mostra solo gli argomenti espliciti
             (cond [(not (eq? (car t) 'app)) (if (null? as) (sexp names t) (cons (sexp names t) as))]
                   [(eq? (cadddr t) 'e) (loop (cadr t) (cons (sexp names (caddr t)) as))]
                   [else (loop (cadr t) as)]))]))
