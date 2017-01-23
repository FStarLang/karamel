open Ulexing
open Parser

let regexp digit = ['0'-'9']
let regexp int = digit+
let regexp low_alpha = ['a'-'z']
let regexp up_alpha =  ['A'-'Z']
let regexp any = up_alpha | low_alpha | '_'
let regexp lident = low_alpha any*
let regexp uident = up_alpha any*

let locate _ tok = tok, Lexing.dummy_pos, Lexing.dummy_pos

let rec token = lexer
| int ->
    let l = utf8_lexeme lexbuf in
    locate lexbuf (INT (int_of_string l))
| uident ->
    let l = utf8_lexeme lexbuf in
    locate lexbuf (UIDENT l)
| "." -> locate lexbuf DOT
| "@" -> locate lexbuf AT
| "-" -> locate lexbuf MINUS
| "+" -> locate lexbuf PLUS
| "," -> locate lexbuf COMMA
| "=" -> locate lexbuf EQUALS
| "*" -> locate lexbuf STAR
| eof -> locate lexbuf EOF
