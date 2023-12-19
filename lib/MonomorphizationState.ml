open Ast
type node = lident * typ list * cg list
type color = Gray | Black
let state: (node, color * lident) Hashtbl.t = Hashtbl.create 41

let resolve t =
  match Hashtbl.find_opt state (flatten_tapp t) with
  | exception Invalid_argument _ -> t
  | Some (_, lid) -> TQualified lid
  | None -> t
