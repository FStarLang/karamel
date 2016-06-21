open PPrint

module K = Constant

let jump ?(indent=2) body =
  jump indent 1 body

let parens_with_nesting contents =
  surround 2 0 lparen contents rparen

let braces_with_nesting contents =
  surround 2 1 lbrace contents rbrace

let int i = string (string_of_int i)

let print_width = function
  | K.UInt8 -> string "uint8"
  | K.UInt16 -> string "uint16"
  | K.UInt32 -> string "uint32"
  | K.UInt64 -> string "uint64"
  | K.Int8 -> string "int8"
  | K.Int16 -> string "int16"
  | K.Int32 -> string "int32"
  | K.Int64 -> string "int64"

let print_constant = function
  | w, s -> string s ^^ print_width w

let print_op = function
  | K.Add -> string "+"
  | K.AddW -> string "+w"
  | K.Sub -> string "-"
  | K.SubW -> string "-"
  | K.Div -> string "/"
  | K.Mult -> string "*"
  | K.Mod -> string "%"
  | K.BOr -> string "|"
  | K.BAnd -> string "&"
  | K.BXor -> string "^"
  | K.BShiftL -> string "<<"
  | K.BShiftR -> string ">>"

let print_lident (idents, ident) =
  separate_map dot string (idents @ [ ident ])

let print_program p decls =
  separate_map (hardline ^^ hardline) p decls

let print_files print_decl files =
  separate_map hardline (fun (f, p) ->
    string (String.uppercase f) ^^ colon ^^ jump (print_program print_decl p)
  ) files

