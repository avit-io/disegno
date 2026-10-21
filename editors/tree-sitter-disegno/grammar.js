// Disegno's tree-sitter grammar: the syntax is Scheme's, with brackets a synonym of
// parentheses (R6RS) and point literals (/out). Highlighting of claim, define, data, types
// and operators is in the queries (queries/highlights.scm), not here.
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
    path: _ => /\/[^\s()\[\];,"]+/,                       // a point: /go/pkg/mod
    symbol: _ => token(choice('/', /[^\s()\[\];,"0-9\/][^\s()\[\];,"]*/)),
  },
});
