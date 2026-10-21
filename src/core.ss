;; Trusted core: printing the plan as GraphQL and HTTP transport to the Dagger session.
;; A plan is a chain of fields: ((container) (from (address "alpine")) (stdout)).

(let loop ([names '("libc.so.6" "libc.musl-x86_64.so.1")])   ; glibc, then musl (Alpine)
  (guard (e [(pair? (cdr names)) (loop (cdr names))]) (load-shared-object (car names))))

;; --- GraphQL ---

(define (json-string s)
  (call-with-string-output-port
    (lambda (p)
      (write-char #\" p)
      (string-for-each
        (lambda (c)
          (case c
            [(#\") (display "\\\"" p)]
            [(#\\) (display "\\\\" p)]
            [(#\newline) (display "\\n" p)]
            [else (if (char<? c #\space)
                      (format p "\\u~4,'0x" (char->integer c))
                      (write-char c p))]))
        s)
      (write-char #\" p))))

(define (gql-value v)
  (cond [(string? v) (json-string v)]
        [(and (pair? v) (eq? (car v) '%input)) (format "{~{~a~^, ~}}" (map (lambda (f) (format "~a: ~a" (car f) (gql-value (cdr f)))) (cdr v)))]
        [(list? v) (format "[~{~a~^, ~}]" (map gql-value v))]
        [(boolean? v) (if v "true" "false")]
        [else (format "~a" v)]))

(define (gql-field f)
  (if (null? (cdr f))
      (symbol->string (car f))
      (format "~a(~{~a~^, ~})" (car f)
              (map (lambda (a) (format "~a: ~a" (car a) (gql-value (cadr a)))) (cdr f)))))

(define (plan->graphql chain)
  (let loop ([c chain])
    (if (null? (cdr c))
        (gql-field (car c))
        (format "~a { ~a }" (gql-field (car c)) (loop (cdr c))))))

;; --- HTTP on localhost, no TLS ---

(define c-socket  (foreign-procedure "socket"  (int int int) int))
(define c-connect (foreign-procedure "connect" (int u8* int) int))
(define c-write   (foreign-procedure "write"   (int u8* size_t) ssize_t))
(define c-read    (foreign-procedure "read"    (int u8* size_t) ssize_t))
(define c-close   (foreign-procedure "close"   (int) int))

(define (sockaddr-localhost port)
  (let ([b (make-bytevector 16 0)])
    (bytevector-u16-native-set! b 0 2)                  ; AF_INET
    (bytevector-u16-set! b 2 port (endianness big))
    (bytevector-u8-set! b 4 127) (bytevector-u8-set! b 7 1)
    b))

(define (base64 bv)
  (define abc "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")
  (let ([n (bytevector-length bv)])
    (call-with-string-output-port
      (lambda (p)
        (do ([i 0 (+ i 3)]) ((>= i n))
          (let* ([byte (lambda (k) (if (< (+ i k) n) (bytevector-u8-ref bv (+ i k)) 0))]
                 [w (+ (* (byte 0) 65536) (* (byte 1) 256) (byte 2))]
                 [ch (lambda (k) (string-ref abc (bitwise-and (bitwise-arithmetic-shift-right w (- 18 (* 6 k))) 63)))])
            (write-char (ch 0) p) (write-char (ch 1) p)
            (write-char (if (< (+ i 1) n) (ch 2) #\=) p)
            (write-char (if (< (+ i 2) n) (ch 3) #\=) p)))))))

(define (write-all fd bv)
  (let loop ([off 0])
    (when (< off (bytevector-length bv))
      (let* ([rest (make-bytevector (- (bytevector-length bv) off))]
             [_ (bytevector-copy! bv off rest 0 (bytevector-length rest))]
             [k (c-write fd rest (bytevector-length rest))])
        (when (< k 0) (error 'http "write failed"))
        (loop (+ off k))))))

(define (read-all fd)
  (let ([buf (make-bytevector 65536)])
    (let-values ([(out get) (open-bytevector-output-port)])
      (let loop ()
        (let ([k (c-read fd buf 65536)])
          (cond [(< k 0) (error 'http "read failed")]
                [(> k 0) (put-bytevector out buf 0 k) (loop)]
                [else (get)]))))))

;; ponytail: HTTP/1.0 and connection close, so no chunked encoding and no keep-alive.
(define (http-post port token path body)
  (let ([fd (c-socket 2 1 0)]                           ; AF_INET, SOCK_STREAM
        [body (string->utf8 body)])
    (unless (zero? (c-connect fd (sockaddr-localhost port) 16))
      (c-close fd) (error 'http "connect failed" port))
    (write-all fd (string->utf8
                    (format "POST ~a HTTP/1.0\r\nHost: 127.0.0.1\r\nAuthorization: Basic ~a\r\nContent-Type: application/json\r\nContent-Length: ~a\r\n\r\n"
                            path (base64 (string->utf8 (string-append token ":"))) (bytevector-length body))))
    (write-all fd body)
    (let ([resp (utf8->string (read-all fd))])
      (c-close fd)
      (let ([i (let loop ([i 0])
                 (cond [(> (+ i 4) (string-length resp)) (error 'http "malformed response" resp)]
                       [(string=? (substring resp i (+ i 4)) "\r\n\r\n") (+ i 4)]
                       [else (loop (+ i 1))]))])
        (substring resp i (string-length resp))))))

;; --- the engine's log stream: server-sent events on /v1/logs, OTLP records as JSON ---
;; Runs in a thread: the read is __collect_safe (on an immobile buffer), so while it waits for a
;; line it does not stop the garbage collector, and with it the main thread. Lines are split
;; on \n bytes, which in UTF-8 never occur inside a character.

(define c-read-safe (foreign-procedure __collect_safe "read" (int u8* size_t) ssize_t))
(define c-shutdown (foreign-procedure "shutdown" (int int) int))
(define (log-stream-stop fd) (c-shutdown fd 2))          ; SHUT_RDWR: a pending read returns too

(define (log-stream port token on-record)               ; on-record gets each record (alist); → fd
  (let ([fd (c-socket 2 1 0)])
    (unless (zero? (c-connect fd (sockaddr-localhost port) 16))
      (c-close fd) (error 'http "connect failed" port))
    (write-all fd (string->utf8
                    (format "GET /v1/logs HTTP/1.0\r\nHost: 127.0.0.1\r\nAuthorization: Basic ~a\r\nAccept: text/event-stream\r\n\r\n"
                            (base64 (string->utf8 (string-append token ":"))))))
    (fork-thread
      (lambda ()
        (let ([buf (make-immobile-bytevector 65536)])
          (let-values ([(line get) (open-bytevector-output-port)])
            (let loop ()
              (let ([k (c-read-safe fd buf 65536)])
                (when (> k 0)
                  (do ([i 0 (+ i 1)]) ((= i k))
                    (let ([b (bytevector-u8-ref buf i)])
                      (if (= b 10) (sse-line (utf8->string (get)) on-record) (put-u8 line b))))
                  (loop))))))))
    fd))

(define (sse-line s on-record)                          ; data: {"resourceLogs":[{"scopeLogs":[{"logRecords":[…]}]}]}
  (when (and (> (string-length s) 7) (string=? (substring s 0 7) "data: {"))
    (for-each (lambda (rl)
                (for-each (lambda (sl) (for-each on-record (json-field sl "logRecords" '())))
                          (json-field rl "scopeLogs" '())))
              (json-field (json-read (substring s 6 (string-length s))) "resourceLogs" '()))))

(define (json-field obj k default) (cond [(and (list? obj) (assoc k obj)) => cdr] [else default]))

;; --- JSON (reading responses only): objects → alists, arrays → lists, null → 'null ---

(define (json-read s)
  (define i 0)
  (define (peek) (string-ref s i))
  (define (skip) (let loop () (when (and (< i (string-length s)) (char-whitespace? (peek))) (set! i (+ i 1)) (loop))))
  (define (eat c) (skip) (unless (char=? (peek) c) (error 'json "expected" c i)) (set! i (+ i 1)))
  (define (word w v) (set! i (+ i (string-length w))) v)
  (define (str)
    (eat #\")
    (call-with-string-output-port
      (lambda (p)
        (let loop ()
          (let ([c (peek)])
            (set! i (+ i 1))
            (cond [(char=? c #\") (void)]
                  [(char=? c #\\)
                   (let ([e (peek)])
                     (set! i (+ i 1))
                     (case e
                       [(#\n) (write-char #\newline p)] [(#\t) (write-char #\tab p)]
                       [(#\r) (write-char #\return p)] [(#\b) (write-char #\backspace p)] [(#\f) (write-char #\page p)]
                       [(#\u) (write-char (integer->char (string->number (substring s i (+ i 4)) 16)) p) (set! i (+ i 4))]
                       [else (write-char e p)]))
                   (loop)]
                  [else (write-char c p) (loop)]))))))
  (define (seq close item)
    (set! i (+ i 1)) (skip)
    (if (char=? (peek) close) (begin (set! i (+ i 1)) '())
        (let loop ([acc (list (item))])
          (skip)
          (if (char=? (peek) #\,) (begin (set! i (+ i 1)) (loop (cons (item) acc)))
              (begin (eat close) (reverse acc))))))
  (define (value)
    (skip)
    (case (peek)
      [(#\{) (seq #\} (lambda () (let ([k (begin (skip) (str))]) (eat #\:) (cons k (value)))))]
      [(#\[) (seq #\] value)]
      [(#\") (str)]
      [(#\t) (word "true" #t)] [(#\f) (word "false" #f)] [(#\n) (word "null" 'null)]
      [else (let ([j i])
              (let loop () (when (and (< i (string-length s)) (memv (peek) (string->list "+-0123456789.eE"))) (set! i (+ i 1)) (loop)))
              (string->number (substring s j i)))]))
  (value))

;; Writing (for the LSP): an alist with string keys is an object, a vector is an array,
;; 'null is null; strings, numbers and booleans as they are.
(define (json-write v p)
  (cond [(string? v) (display (json-string v) p)]
        [(boolean? v) (display (if v "true" "false") p)]
        [(eq? v 'null) (display "null" p)]
        [(number? v) (display v p)]
        [(vector? v) (display "[" p)
                     (let loop ([i 0])
                       (when (< i (vector-length v))
                         (when (> i 0) (display "," p))
                         (json-write (vector-ref v i) p)
                         (loop (+ i 1))))
                     (display "]" p)]
        [(and (pair? v) (pair? (car v)) (string? (caar v)))
         (display "{" p)
         (let loop ([kv v] [first #t])
           (unless (null? kv)
             (unless first (display "," p))
             (display (json-string (caar kv)) p) (display ":" p) (json-write (cdar kv) p)
             (loop (cdr kv) #f)))
         (display "}" p)]
        [else (error 'json "value not serializable" v)]))

(define (json->string v) (call-with-string-output-port (lambda (p) (json-write v p))))

;; --- Session ---

(define (query text)                                    ; GraphQL document → JSON response (text)
  (let ([port (getenv "DAGGER_SESSION_PORT")] [token (getenv "DAGGER_SESSION_TOKEN")])
    (unless (and port token) (error 'submit "no session: run under `dagger api with-session`"))
    (http-post (string->number port) token "/query" (format "{\"query\": ~a}" (json-string text)))))

(define (submit chain) (query (format "{ ~a }" (plan->graphql chain))))

;; Sends the chain and returns the leaf's value; engine errors become errors.
(define (submit-leaf chain)
  (let* ([r (json-read (submit chain))] [errs (assoc "errors" r)])
    (when (and errs (pair? (cdr errs)))
      (error 'engine (cdr (or (assoc "message" (cadr errs)) (cons #f "error")))   ; the extensions (EXEC_ERROR:
             (cond [(assoc "extensions" (cadr errs)) => cdr] [else '()])))         ; cmd, exitCode, stderr) are kept

    (let loop ([v (cdr (assoc "data" r))])
      (if (and (pair? v) (pair? (car v)) (string? (caar v))) (loop (cdar v)) v))))
