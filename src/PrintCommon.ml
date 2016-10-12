open PPrint
open Constant

let break1 = break 1

let jump ?(indent=2) body =
  jump indent 1 body

let parens_with_nesting contents =
  surround 2 0 lparen contents rparen

let braces_with_nesting contents =
  surround 2 1 lbrace contents rbrace

let int i = string (string_of_int i)

let print_width = function
  | UInt -> string "uintmax"
  | UInt8 -> string "uint8"
  | UInt16 -> string "uint16"
  | UInt32 -> string "uint32"
  | UInt64 -> string "uint64"
  | Int -> string "intmax"
  | Int8 -> string "int8"
  | Int16 -> string "int16"
  | Int32 -> string "int32"
  | Int64 -> string "int64"
  | Bool -> string "bool"

let print_constant = function
  | w, s -> string s ^^ print_width w

let print_op = function
  | Add -> string "+"
  | AddW -> string "+w"
  | Sub -> string "-"
  | SubW -> string "-"
  | Div -> string "/"
  | DivW -> string "/w"
  | Mult -> string "*"
  | MultW -> string "*w"
  | Mod -> string "%"
  | BOr -> string "|"
  | BAnd -> string "&"
  | BXor -> string "^"
  | BNot -> string "~"
  | BShiftL -> string "<<"
  | BShiftR -> string ">>"
  | Eq -> string "=="
  | Neq -> string "!="
  | Lt -> string "<"
  | Lte -> string "<="
  | Gt -> string ">"
  | Gte -> string ">="
  | And -> string "&&"
  | Or -> string "||"
  | Xor -> string "^"
  | Not -> string "!"
  | PostIncr | PreIncr -> string "++"
  | PostDecr | PreDecr -> string "--"
  | Assign -> string "="
  | Comma -> string ","

let print_lident (idents, ident) =
  separate_map dot string (idents @ [ ident ])

let print_program p decls =
  separate_map (hardline ^^ hardline) p decls

let print_files print_decl files =
  separate_map hardline (fun (f, p) ->
    string (String.uppercase f) ^^ colon ^^ jump (print_program print_decl p)
  ) files

let printf_of_pprint f =
  fun buf t ->
    PPrint.ToBuffer.compact buf (f t)

let printf_of_pprint_pretty f =
  fun buf t ->
    PPrint.ToBuffer.pretty 0.95 Utils.twidth buf (f t)

let pdoc buf d =
  PPrint.ToBuffer.compact buf d
