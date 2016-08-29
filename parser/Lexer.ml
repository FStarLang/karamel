open Ulexing
open Parser

let regexp digit = ['0'-'9']
let regexp int = digit+

let locate _ tok = tok, Lexing.dummy_pos, Lexing.dummy_pos

let rec token = lexer
| int ->
    let l = utf8_lexeme lexbuf in
    locate lexbuf (INT (int_of_string l))
| "." -> locate lexbuf DOT
| "@" -> locate lexbuf AT
| "-" -> locate lexbuf MINUS
| "+" -> locate lexbuf PLUS
| eof -> locate lexbuf EOF
