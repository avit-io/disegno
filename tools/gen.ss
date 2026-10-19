;; Genera engine.disegno dallo schema del motore (introspezione sulla sessione).
;; Uso: dagger api with-session scheme --script tools/gen.ss
;;
;; Il piano è un dato: ogni campo del motore diventa un costruttore della famiglia
;; (data Obj : (→ Kind Type) ...), indicizzata dal tipo GraphQL (Kind.container, ...).
;; Il nome del costruttore dà il campo (Container.with-exec → withExec), i binder gli argomenti.
;; Solo i tipi in `allowed`, solo gli argomenti obbligatori e quelli promossi (`promoted`); i campi
;; non esprimibili si saltano.
;; Un risultato Boolean diventa un'osservazione, (Obj Kind.bool).
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

(define (camel s)                                        ; with-new-file → withNewFile (come in plan.ss)
  (let loop ([cs (string->list s)] [up #f])
    (cond [(null? cs) ""]
          [(char=? (car cs) #\-) (loop (cdr cs) #t)]
          [else (string-append (string (if up (char-upcase (car cs)) (car cs))) (loop (cdr cs) #f))])))

(define (obj k) (list 'Obj (string->symbol (string-append "Kind." (kebab k)))))

(define (expected a)                                     ; gli ID sono generici: il tipo sta in @expectedType
  (let ([d (find (lambda (d) (equal? (get d "name") "expectedType")) (get a "directives"))])
    (and d (json-read (get (car (get d "args")) "value")))))

;; Tipi raffinati per nome d'argomento: lo schema dice String, il disegno sa di più.
;; ponytail: regola per nome, basta per Dagger; se un nome cambia senso servirà una tabella per campo.
(define refined '(("path" String Abs) ("address" String Image) ("args" (List String) (List Arg)) ("port" Nat Port)))

(define (arg-type a)
  (let ([t (base-type a)] [r (assoc (get a "name") refined)])
    (if (and r (equal? t (cadr r))) (caddr r) t)))

(define (base-type a)
  (let loop ([t (get a "type")])
    (let ([k (get t "kind")] [n (get t "name")])
      (cond [(equal? k "NON_NULL") (loop (get t "ofType"))]
            [(equal? k "LIST") (and (eq? (loop (get t "ofType")) 'String) '(List String))]
            [(equal? n "String") 'String]
            [(equal? n "Int") 'Nat]                     ; ponytail: Int → Nat, bastano porte e conteggi
            [(equal? n "Boolean") 'Bool]
            [(equal? n "ID") (let ([e (expected a)]) (and e (member e allowed) (obj e)))]
            [else #f]))))

(define (result-type t)
  (let ([k (get t "kind")] [n (get t "name")])
    (cond [(equal? k "NON_NULL") (result-type (get t "ofType"))]
          [(and (equal? k "OBJECT") (member n allowed)) (obj n)]
          [(and (equal? k "SCALAR") (equal? n "Boolean")) (obj "bool")]
          [else #f])))

(define (required? a) (and (equal? (get (get a "type") "kind") "NON_NULL") (eq? (get a "defaultValue") 'null)))

;; Argomenti opzionali promossi: per questi campi il costruttore li chiede, nell'ordine dello
;; schema. Chi non ne ha bisogno usa un nome curato della libreria, che passa il default.
;; ponytail: un elenco a mano, campo per campo; si allunga quando una libreria ne ha bisogno.
(define promoted
  '(("Directory" "filter" "include" "exclude")           ; i glob dei file da tenere e da togliere
    ("Directory" "withNewFile" "permissions")            ; un file eseguibile
    ("Container" "asService" "useEntrypoint")))          ; un service con l'entrypoint dell'immagine

(define (wanted? type n a)
  (or (required? a)
      (let ([p (find (lambda (p) (and (equal? (car p) type) (equal? (cadr p) n))) promoted)])
        (and p (member (get a "name") (cddr p)) #t))))

;; Costruttore: (nome ((argomento tipo) ...) risultato), o #f se il campo non è esprimibile.
(define (constructor type f)
  (let* ([n (get f "name")]
         [args (filter (lambda (a) (wanted? type n a)) (get f "args"))]
         [ats (map arg-type args)]
         [res (result-type (get f "type"))])
    (and res (not (get f "isDeprecated")) (for-all values ats) (not (and (equal? type "Query") (member n excluded)))
         (string=? (camel (kebab n)) n)                  ; il runner deve poter risalire al campo
         (list (string->symbol (format "~a.~a" type (kebab n)))
               (append (if (equal? type "Query") '() (list (list 'self (obj type))))
                       (map (lambda (a t) (list (string->symbol (get a "name")) t)) args ats))
               res))))

(define (constructors type)
  (filter values (map (lambda (f) (constructor type f))
                      (list-sort (lambda (a b) (string<? (get a "name") (get b "name")))   ; lo schema 1.0 non è in ordine
                                 (get (find (lambda (t) (equal? (get t "name") type)) schema) "fields")))))

;; Snodi del nucleo: costruttori anch'essi, ma li realizza il runner (plan.ss).
(define nucleo
  `((%host-dir ((path String)) ,(obj "directory"))
    (%host-secret ((name String)) ,(obj "secret"))       ; il segreto di una variabile d'ambiente dell'host
    (try-exec ((self ,(obj "container")) (args (List Arg))) ,(obj "container"))
    (passes? ((self ,(obj "container"))) ,(obj "bool"))
    (branch ((cond ,(obj "bool")) (then (Obj k)) (else (Obj k))) (Obj k))
    (overlay ((path String) (dir ,(obj "directory"))) ,(obj "export"))
    (replace ((path String) (dir ,(obj "directory"))) ,(obj "export"))
    (publish ((self ,(obj "container")) (address Image)) ,(obj "export"))
    ;; Effetti in sequenza: apply esegue un comando come effetto (fuori dalla cache), then
    ;; realizza due uscite in ordine, skip è l'uscita vuota, probe osserva il mondo fuori dalla cache.
    (apply ((self ,(obj "container")) (args (List Arg))) ,(obj "export"))
    (then ((first ,(obj "export")) (second ,(obj "export"))) ,(obj "export"))
    (skip () ,(obj "export"))
    ;; Un service in background: avviato qui, resta vivo fino alla fine della sessione, e i passi
    ;; che lo legano usano questa istanza. Senza start, Dagger lo ferma quando nessuno lo usa.
    (start ((self ,(obj "service"))) ,(obj "export"))
    (probe ((self ,(obj "container")) (args (List Arg))) ,(obj "bool"))
    ;; Un segreto letto a esecuzione: cmd, in self, lo stampa; il runner lo passa a Dagger
    ;; (setSecret) quando un passo lo usa. Il valore non torna mai al linguaggio.
    (secret-from ((self ,(obj "container")) (args (List Arg))) ,(obj "secret"))
    ;; L'unico stato che persiste tra un'esecuzione e l'altra, non indirizzato per contenuto:
    ;; per questo è uno snodo dichiarato e non un campo generato.
    (cache-volume ((key String)) ,(obj "cache-volume"))))

(define excluded '("cacheVolume"                     ; campi radice resi snodi del nucleo
                   "secret" "setSecret"))            ; un segreto entra solo dalla firma di main (Host-secret)

(define all (append nucleo (apply append (map constructors (cons "Query" allowed)))))

(define (signature c)
  (if (null? (cadr c)) (caddr c)
      (format "(→ ~a~a)" (apply string-append (map (lambda (b) (format "[~a ~a] " (car b) (cadr b))) (cadr c))) (caddr c))))

(define (obj? t) (and (pair? t) (eq? (car t) 'Obj)))

;; nodes: tutti i sotto-piani, per ricorsione strutturale su ogni costruttore.
(define (nodes-clause c)
  (let* ([xs (map (lambda (i) (string->symbol (format "x~a" i))) (iota (length (cadr c))))]
         [self (if (null? xs) (car c) (cons (car c) xs))]
         [subs (filter values (map (lambda (b x) (and (obj? (cadr b)) x)) (cadr c) xs))])
    (format "  [~a] (:: (any ~a) ~a)"
            self self (fold-right (lambda (x acc) (format "(++ (nodes ~a) ~a)" x acc)) "vuota" subs))))

;; chain: i nodi lungo la catena di self (un container e i suoi passi), senza scendere negli
;; argomenti; branch prosegue in entrambi i rami.
(define (chain-clause c)
  (let* ([xs (map (lambda (i) (string->symbol (format "x~a" i))) (iota (length (cadr c))))]
         [self (if (null? xs) (car c) (cons (car c) xs))]
         [rest (cond [(eq? (car c) 'branch) "(++ (chain x1) (chain x2))"]
                     [(and (pair? (cadr c)) (eq? (car (car (cadr c))) 'self)) "(chain x0)"]
                     [else "vuota"])])
    (format "  [~a] (:: (any ~a) ~a)" self self rest)))

(call-with-output-file (at-root "lib/engine.disegno")
  (lambda (p)
    (format p "; Generato da gen.ss dallo schema di Dagger: non modificare a mano.~%~%")
    (format p "(data Kind~%~{  [~a]~^~%~})~%~%"
            (map (lambda (k) (cadr (obj k))) (append allowed '("bool" "export"))))
    (format p "(data Obj : (→ Kind Type)~%~{  [~a : ~a]~^~%~})~%(builtin obj Obj)~%~%"
            (apply append (map (lambda (c) (list (car c) (signature c))) all)))
    (for-each (lambda (k) (format p "(def ~a : Type~%  ~a)~%~%" k (obj k))) allowed)
    (format p "; Un sotto-piano qualsiasi, di qualunque tipo.~%(data Any~%  [any (Obj k)])~%~%")
    (format p "(def nodes : (→ (Obj k) (List Any))~%~{~a~^~%~})~%~%" (map nodes-clause all))
    (format p "(def chain : (→ (Obj k) (List Any))~%~{~a~^~%~})~%" (map chain-clause all)))
  'replace)
(format #t "engine.disegno scritto: ~a costruttori~%" (length all))
