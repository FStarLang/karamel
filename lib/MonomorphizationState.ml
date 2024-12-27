open Ast
open PrintAst.Ops

(* Various bits of state for monomorphization, the two most important being
   `state` (type monomorphization) and `generated_lids` (function
   monomorphization). *)

(* Monomorphization of data types. *)
type node = lident * typ list * cg list
type color = Gray | Black

(* Each polymorphic type `lid` applied to types `ts` and const generics `ts`
   appears in `state`, and maps to `monomorphized_lid`, the name of its
   monomorphized instance. *)
let state: (node, color * lident) Hashtbl.t = Hashtbl.create 41

(* Because of polymorphic externals, one still encounters,
   post-monomorphizations, application nodes in types (e.g. after instantiating
   a polymorphic type scheme). The `resolve*` functions, below, normalize a type
   to only contain monomorphic type names (and no more type applications) *)
let resolve t: typ =
  match t with
  | TApp _ | TCgApp _ when Hashtbl.mem state (flatten_tapp t) ->
      TQualified (snd (Hashtbl.find state (flatten_tapp t)))
  | TTuple ts when Hashtbl.mem state (tuple_lid, ts, []) ->
      TQualified (snd (Hashtbl.find state (tuple_lid, ts, [])))
  | _ ->
      t

let resolve_deep = (object(self)
  inherit [_] map

  method! visit_TApp () t ts =
    let ts = List.map (self#visit_typ ()) ts in
    resolve (TApp (t, ts))

  method! visit_TCgApp () t ts =
    resolve (TCgApp (t, ts))

  method! visit_TTuple () ts =
    let ts = List.map (self#visit_typ ()) ts in
    resolve (TTuple ts)
end)#visit_typ ()

(* Monomorphization of functions *)
type reverse_mapping = (lident * expr list * typ list, lident) Hashtbl.t

let generated_lids: reverse_mapping = Hashtbl.create 41

let debug () =
  Hashtbl.iter (fun (lid, ts, cgs) (_, monomorphized_lid) ->
    KPrint.bprintf "%a <%a> <%a> ~~> %a\n" plid lid pcgs cgs ptyps ts plid
    monomorphized_lid
  ) state;
  Hashtbl.iter (fun (lid, es, ts) monomorphized_lid ->
    KPrint.bprintf "%a <%a> <%a> ~~> %a\n" plid lid pexprs es ptyps ts plid
    monomorphized_lid
  ) generated_lids
