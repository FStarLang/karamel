open Sedlexing
open KParser

let digit = [%sedlex.regexp? '0'..'9']
let integer = [%sedlex.regexp? Plus digit]
let low_alpha = [%sedlex.regexp? 'a'..'z']
let up_alpha =  [%sedlex.regexp? 'A'..'Z']
let any = [%sedlex.regexp? up_alpha | low_alpha | '_' | '-' | digit]
let lident = [%sedlex.regexp? low_alpha, Star (any)]
let uident = [%sedlex.regexp? up_alpha, Star (any)]

let locate _ tok = tok, Lexing.dummy_pos, Lexing.dummy_pos

let keywords = [
  "rename", RENAME;
  "rename-prefix", RENAME_PREFIX
]

let rec token lexbuf =
match%sedlex lexbuf with
| integer ->
    let l = Utf8.lexeme lexbuf in
    locate lexbuf (INT (int_of_string l))
| uident ->
    let l = Utf8.lexeme lexbuf in
    locate lexbuf (UIDENT l)
| lident ->
    let l = Utf8.lexeme lexbuf in
    begin try
      locate lexbuf (List.assoc l keywords)
    with Not_found ->
      locate lexbuf (LIDENT l)
    end
| "." -> locate lexbuf DOT
| "@" -> locate lexbuf AT
| "-" -> locate lexbuf MINUS
| "+" -> locate lexbuf PLUS
| "," -> locate lexbuf COMMA
| "=" -> locate lexbuf EQUALS
| "*" -> locate lexbuf STAR
| "\\*" -> locate lexbuf STAR
| "[" -> locate lexbuf LBRACK
| "]" -> locate lexbuf RBRACK
| eof -> locate lexbuf EOF
| _ -> assert false
