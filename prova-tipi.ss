;; Controllo del type checker: gli esempi passano, le scappatoie vengono rifiutate.
(load "tipi.ss")

(check-file "base.disegno")
(check-file "esempi.disegno")

(define (contiene? s sub)
  (let ([n (string-length s)] [k (string-length sub)])
    (let loop ([i 0]) (and (<= (+ i k) n) (or (string=? (substring s i (+ i k)) sub) (loop (+ i 1)))))))

(define (rifiuta src atteso)
  (let ([msg (guard (e [(message-condition? e) (condition-message e)]) (check-string src) #f)])
    (unless (and msg (contiene? msg atteso))
      (error 'prova (format "~a: atteso un errore con «~a», ottenuto ~s" src atteso msg)))))

(check-string "(data ⊥ : Type)")
(rifiuta "(def assurdo : ⊥ assurdo)" "ricorsione non strutturale")
(rifiuta "(def postulato : ⊥)" "manca la definizione")
(rifiuta "(data Cattivo [mk (→ Cattivo ⊥)])" "strettamente positiva")
(rifiuta "(def tt : Type Type)" "atteso")
(rifiuta "(data U : Type [u : (→ Type U)])" "livello")
(rifiuta "(def pred : (→ Nat Nat) [(add1 k)] k)" "manca il caso")
(rifiuta "(def giro : (→ Nat Nat) [n] (giro n))" "ricorsione non strutturale")
(rifiuta "(def falso : (≡ 1 2) refl)" "atteso")
(rifiuta "(def testa-vuota : (→ (Vec A 0) A) [nil] nil)" "atteso")
(display "ok\n")
