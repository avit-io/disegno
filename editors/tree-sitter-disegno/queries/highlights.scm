; Evidenziazione di Disegno. Le forme si riconoscono dal primo simbolo della lista.

(comment) @comment
(string) @string
(number) @number
(path) @string.special.path

; Le dichiarazioni e il nome che introducono.
(list . (symbol) @keyword
  (#any-of? @keyword "claim" "define" "data" "record" "extern" "import" "builtin"))
(list . (symbol) @_kw . (symbol) @function
  (#any-of? @_kw "claim" "define"))
(list . (symbol) @_kw . (list . (symbol) @function)
  (#eq? @_kw "define"))
(list . (symbol) @_kw . (symbol) @type.definition
  (#any-of? @_kw "data" "record"))

; Le forme speciali.
(list . (symbol) @keyword.control
  (#any-of? @keyword.control "let" "let*" "λ" "lambda" "match" "match*" "cond" "when" "unless" "begin" "pipe" "branch" "if" "the" "list"))
((symbol) @keyword.control
  (#eq? @keyword.control "else"))

; I tipi: un nome con l'iniziale maiuscola (Nat, Container, Obj.…), l'universo e i quantificatori.
((symbol) @type
  (#match? @type "^[A-Z]"))
((symbol) @keyword.type
  (#any-of? @keyword.type "Π" "∀"))

; Prove ed elementi speciali.
((symbol) @constant.builtin
  (#any-of? @constant.builtin "auto" "refl" "tt" "true" "false" "root" "here" "vuota" "_" "TODO"))

; Gli operatori: frecce, uguaglianza, relazioni e spazi affini.
((symbol) @operator
  (#any-of? @operator "→" ":" "≡" "⊑" "⋔" "¬" "⊕" "⊖" "/" "++" "+" "∸" "*" "≤" "≥" "×" "::"))

["(" ")" "[" "]"] @punctuation.bracket
