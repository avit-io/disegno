; Disegno highlighting. Forms are recognized by the first symbol of the list.

(comment) @comment
(string) @string
(number) @number
(path) @string.special.path

; Declarations and the name they introduce.
(list . (symbol) @keyword
  (#any-of? @keyword "claim" "define" "data" "record" "extern" "import" "builtin"))
(list . (symbol) @_kw . (symbol) @function
  (#any-of? @_kw "claim" "define"))
(list . (symbol) @_kw . (list . (symbol) @function)
  (#eq? @_kw "define"))
(list . (symbol) @_kw . (symbol) @type.definition
  (#any-of? @_kw "data" "record"))

; Special forms.
(list . (symbol) @keyword.control
  (#any-of? @keyword.control "let" "let*" "λ" "lambda" "match" "match*" "cond" "when" "unless" "begin" "pipe" "branch" "if" "the" "list"))
((symbol) @keyword.control
  (#eq? @keyword.control "else"))

; Types: a capitalized name (Nat, Container, Obj.…), the universe and the quantifiers.
((symbol) @type
  (#match? @type "^[A-Z]"))
((symbol) @keyword.type
  (#any-of? @keyword.type "Π" "∀"))

; Proofs and special elements.
((symbol) @constant.builtin
  (#any-of? @constant.builtin "auto" "refl" "tt" "true" "false" "root" "here" "nil" "_" "TODO"))

; Operators: arrows, equality, relations and affine spaces.
((symbol) @operator
  (#any-of? @operator "→" ":" "≡" "⊑" "⋔" "¬" "⊕" "⊖" "/" "++" "+" "∸" "*" "≤" "≥" "×" "::"))

["(" ")" "[" "]"] @punctuation.bracket
