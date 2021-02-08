(* Some user-provided type abbreviations that can guide the name-generation for
   monomorphized data type instances.

   Usage (in F* ):

   let my-name = t t1 t2

   Then nudges kremlin to pick <my-name> for the typedef struct used for the
   monomorphic instance of t specialized for t1 and t2.
*)

open Ast
open PrintAst.Ops

(* Filled by Inlining.ml, patched-up by DataTypes.ml during unused type argument
   elimination / unit field elimination. *)
let hints: ((lident * typ list) * lident) list ref = ref []

let debug () =
  KPrint.bprintf "==== state of naming hints ====\n";
  List.iter (fun ((hd, args), lid) ->
    KPrint.bprintf "%a --> %a\n" ptyp (TApp (hd, args)) plid lid
  ) !hints
