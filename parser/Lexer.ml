open Ulexing
open Parser

let regexp digit = ['0'-'9']
let regexp int = digit+
let regexp low_alpha = ['a'-'z']
let regexp up_alpha =  ['A'-'Z']
let regexp any = up_alpha | low_alpha | '_' | digit
let regexp lident = low_alpha any*
let regexp uident = up_alpha any*

let locate _ tok = tok, Lexing.dummy_pos, Lexing.dummy_pos

let keywords = [
  "public", PUBLIC
]

let rec token = lexer
| int ->
    let l = utf8_lexeme lexbuf in
    locate lexbuf (INT (int_of_string l))
| uident ->
    let l = utf8_lexeme lexbuf in
    locate lexbuf (UIDENT l)
| lident ->
    let l = utf8_lexeme lexbuf in
    begin try
      locate lexbuf (List.assoc l keywords)
    with Not_found ->
      Printf.fprintf stderr "invalid keyword: %s" l;
      exit 1
    end
| "." -> locate lexbuf DOT
| "@" -> locate lexbuf AT
| "-" -> locate lexbuf MINUS
| "+" -> locate lexbuf PLUS
| "," -> locate lexbuf COMMA
| "=" -> locate lexbuf EQUALS
| "*" -> locate lexbuf STAR
| "\\*" -> locate lexbuf STAR
| "(" -> locate lexbuf LPAREN
| ")" -> locate lexbuf RPAREN
| eof -> locate lexbuf EOF
