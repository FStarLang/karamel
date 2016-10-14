open CStar

module W = Wasmlib

let dummy_pos =
  W.Source.({ file = ""; line = 0; column = 0 })

let dummy_region =
  W.Source.({ left = dummy_pos; right = dummy_pos })

let dummy_phrase what =
  W.Source.({ at = dummy_region; it = what })

let mk_module (_files: (string * program) list): W.Ast.module_ =
  dummy_phrase W.Ast.empty_module
