// Grammatica tree-sitter di Disegno: la sintassi è quella di Scheme, con le quadre sinonimo
// delle tonde (R6RS) e i letterali di punto (/out). L'evidenziazione
// di claim, define, data, tipi e operatori sta nelle query (queries/highlights.scm), non qui.
module.exports = grammar({
  name: 'disegno',

  extras: $ => [/\s/, $.comment],

  rules: {
    source_file: $ => repeat($._form),

    _form: $ => choice($.list, $.bracket, $.string, $.number, $.path, $.symbol),

    list: $ => seq('(', repeat($._form), ')'),
    bracket: $ => seq('[', repeat($._form), ']'),

    comment: _ => token(seq(';', /.*/)),
    string: _ => token(seq('"', repeat(choice(/[^"\\]/, /\\./)), '"')),
    number: _ => /[0-9]+/,
    path: _ => /\/[^\s()\[\];,"]+/,                       // un punto: /go/pkg/mod
    symbol: _ => token(choice('/', /[^\s()\[\];,"0-9\/][^\s()\[\];,"]*/)),
  },
});
