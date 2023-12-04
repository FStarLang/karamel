open Ast
type node = lident * typ list
type color = Gray | Black
let state: (node, color * lident) Hashtbl.t = Hashtbl.create 41
