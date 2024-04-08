open Ast
open PrintAst.Ops

type node = lident * typ list * cg list
type color = Gray | Black
let state: (node, color * lident) Hashtbl.t = Hashtbl.create 41

let resolve t =
  match Hashtbl.find_opt state (flatten_tapp t) with
  | exception Invalid_argument _ -> t
  | Some (_, lid) -> TQualified lid
  | None -> t

let debug () =
  KPrint.bprintf "MONOMORPHIZATION STATE:\n";
  Hashtbl.iter (fun (lid, t, cgs) _ ->
    KPrint.bprintf "  %a: %a ++ %a\n" plid lid ptyps t pcgs cgs
  ) state
