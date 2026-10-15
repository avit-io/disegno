; Evidenziazione di Disegno. Le forme si riconoscono dal primo simbolo della lista.

(comment) @comment
(string) @string
(number) @number
(path) @string.special.path

; Le dichiarazioni e il nome che introducono.
(list . (symbol) @keyword
  (#any-of? @keyword "def" "data" "record" "extern" "include"))
(list . (symbol) @_kw . (symbol) @function
  (#eq? @_kw "def"))
(list . (symbol) @_kw . (symbol) @type.definition
  (#any-of? @_kw "data" "record"))

; Le forme speciali.
(list . (symbol) @keyword.control
  (#any-of? @keyword.control "let" "pipe" "branch" "if"))

; I tipi: un nome con l'iniziale maiuscola (Nat, Container, Obj.…) e l'universo.
((symbol) @type
  (#match? @type "^[A-Z]"))

; Prove ed elementi speciali.
((symbol) @constant.builtin
  (#any-of? @constant.builtin "auto" "refl" "tt" "true" "false" "root" "here" "vuota" "_"))

; Gli operatori: frecce, uguaglianza, relazioni e spazi affini.
((symbol) @operator
  (#any-of? @operator "→" ":" "≡" "⊑" "⋔" "¬" "⊕" "⊖" "/" "++" "+" "∸" "*" "≤" "≥" "×" "::"))

; Clausole e binder: le quadre.
["(" ")" "[" "]"] @punctuation.bracket
