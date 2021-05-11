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

let record files =
  let gc_map = Helpers.build_map files (fun map -> function
    | DType (lid, flags, _, _) when List.mem Common.GcType flags -> Hashtbl.add map lid ()
    | _ -> ()
  ) in

  (object
    inherit [_] iter

    method visit_DType _ lid _ n def =
      match def with
      | Abbrev (TApp (hd, args))
        when List.assoc_opt (hd, args) !hints = None &&
        not (Hashtbl.mem gc_map hd) &&
        n = 0 ->
          (* Don't use a type abbreviation towards a to-be-GC'd type as a
           * hint, because there will be a mismatch later on with a * being
           * added. This is mosly for backwards-compat with miTLS having
           * hand-written code in mitlsffi.c. *)
          hints := ((hd, args), lid) :: !hints

      | Abbrev (TTuple args)
        when List.assoc_opt (tuple_lid, args) !hints = None &&
        n = 0 ->
          hints := ((tuple_lid, args), lid) :: !hints

      | _ ->
          ()
  end)#visit_files () files;

  if Options.debug "names" then
    debug ()
