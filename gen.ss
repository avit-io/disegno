;; Genera engine.disegno dallo schema del motore (introspezione sulla sessione).
;; Uso: dagger run scheme --script gen.ss
;; Solo i tipi in `allowed`, solo gli argomenti obbligatori; i campi con argomenti o risultati
;; non esprimibili si saltano. Un risultato Boolean diventa un'osservazione (Remote Bool).
(load "core.ss")

(define allowed '("Container" "Directory" "File" "CacheVolume" "GitRepository" "GitRef"))

(define typeref "type { kind name ofType { kind name ofType { kind name ofType { kind name } } } }")
(define schema
  (let ([r (json-read (query (format "{ __schema { types { name kind fields { name isDeprecated args { name defaultValue directives { name args { name value } } ~a } ~a } } } }"
                                     typeref typeref)))])
    (cdr (assoc "types" (cdr (assoc "__schema" (cdr (assoc "data" r))))))))

(define (get o k) (cdr (assoc k o)))

(define (scalar name)                                    ; tipo di un argomento
  (cond [(equal? name "String") 'String]
        [(equal? name "Int") 'Nat]                      ; ponytail: Int → Nat, bastano porte e conteggi
        [(equal? name "Boolean") 'Bool]
        [(and (> (string-length name) 2) (string=? (substring name (- (string-length name) 2) (string-length name)) "ID")
              (member (substring name 0 (- (string-length name) 2)) allowed))
         (string->symbol (substring name 0 (- (string-length name) 2)))]
        [else #f]))

;; Gli argomenti oggetto sono ID generici; il tipo vero sta nella direttiva @expectedType(name: "Directory").
(define (expected a)
  (let ([d (find (lambda (d) (equal? (get d "name") "expectedType")) (get a "directives"))])
    (and d (let ([v (get (car (get d "args")) "value")]) (json-read v)))))

(define (arg-type a)
  (let loop ([t (get a "type")])
    (let ([k (get t "kind")])
      (cond [(equal? k "NON_NULL") (loop (get t "ofType"))]
            [(equal? k "LIST") (and (eq? (loop (get t "ofType")) 'String) '(List String))]
            [(and (equal? k "SCALAR") (equal? (get t "name") "ID"))
             (let ([e (expected a)]) (and e (member e allowed) (string->symbol e)))]
            [(equal? k "SCALAR") (scalar (get t "name"))]
            [else #f]))))

(define (result-type t)
  (let ([k (get t "kind")] [n (get t "name")])
    (cond [(equal? k "NON_NULL") (result-type (get t "ofType"))]
          [(and (equal? k "OBJECT") (member n allowed)) (string->symbol n)]
          [(and (equal? k "SCALAR") (equal? n "Boolean")) '(Remote Bool)]
          [else #f])))

(define (kebab s)                                        ; withNewFile → with-new-file
  (list->string
    (let loop ([cs (string->list s)] [prev #f])
      (cond [(null? cs) '()]
            [(and (char-upper-case? (car cs)) prev (not (char-upper-case? prev)))
             (cons* #\- (char-downcase (car cs)) (loop (cdr cs) (car cs)))]
            [else (cons (char-downcase (car cs)) (loop (cdr cs) (car cs)))]))))

(define (required? a) (and (equal? (get (get a "type") "kind") "NON_NULL") (eq? (get a "defaultValue") 'null)))

;; → stringa della dichiarazione, o #f se il campo non è esprimibile
(define (field-decl type f)
  (let* ([root? (equal? type "Query")]
         [args (filter required? (get f "args"))]
         [ats (map arg-type args)]
         [res (result-type (get f "type"))])
    (and res (not (get f "isDeprecated")) (for-all values ats)
         (not (let ([n (get f "name")]) (and (> (string-length n) 6) (string=? (substring n (- (string-length n) 6) (string-length n)) "FromID"))))
         (let ([binders (append (if root? '() (list (format "[self ~a]" type)))
                                (map (lambda (a t) (format "[~a ~a]" (get a "name") t)) args ats))])
           (format "(extern ~a.~a : ~a ~a)"
                   type (kebab (get f "name"))
                   (if (null? binders) res (format "(→ ~a~a)" (apply string-append (map (lambda (b) (string-append b " ")) binders)) res))
                   (if root? (get f "name") (format "~a.~a" type (get f "name"))))))))

(define (decls type)
  (let ([t (find (lambda (t) (equal? (get t "name") type)) schema)])
    (filter values (map (lambda (f) (field-decl type f)) (get t "fields")))))

(call-with-output-file "engine.disegno"
  (lambda (p)
    (format p "; Generato da gen.ss dallo schema di Dagger: non modificare a mano.~%~%")
    (for-each (lambda (n) (format p "(extern ~a : Type ~a)~%" n n)) allowed)
    (for-each (lambda (type)
                (format p "~%; --- ~a ---~%~%" type)
                (for-each (lambda (d) (format p "~a~%" d)) (decls type)))
              (cons "Query" allowed)))
  'replace)
(display "engine.disegno scritto\n")
