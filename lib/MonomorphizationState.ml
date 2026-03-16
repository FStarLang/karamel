open Ast
open PrintAst.Ops

(* Various bits of state for monomorphization, the two most important being
   `state` (type monomorphization) and `generated_lids` (function
   monomorphization). *)

(* Monomorphization of data types *********************************************)
type node = lident * typ list * cg list

(* Our graph traversal is complicated! *)
type color =
  | White
    (* We have allocated a name for this node, and done nothing else. It should
       be traversed. *)
  | Gray
    (* We are in the midst of a traversal and we are hitting a node that appears
       in our call stack. If we we are not under a reference (pointer), then
       this may be a cycle. *)
  | BlackForward
    (* We have visited this node, but all we have done is emit a forward
       declaration for it. It should be visited again (via the
       `pending_declarations` table) when we see the polymorphic declaration. *)
  | Black
    (* We have visited this node and have emitted a full declaration for it.
       Nothing left to do. *)
[@@ deriving show]

(* Each polymorphic type `lid` applied to types `ts` and const generics `ts`
   appears in `state`, and maps to `monomorphized_lid`, the name of its
   monomorphized instance. *)
let state: (node, color * lident) Hashtbl.t = Hashtbl.create 41


(* Name management ************************************************************)

(* Generally speaking, we want to go from types that contain applications
   (potentially at depth), to types that contain no such things.

   The first use-case is for allocating names during the polymorphic type
   traversal -- in the example of `t<u<v>>` found under a reference, we want to
   allocate names for `u<v>, then for `t<u__v>`, preserving our invariant that
   keys in `state` do NOT contain `TApp` or `TCgApp` nodes.

   The second use-case is for polymorphic externals. Long after
   monomorphization, we may still end up with `u<v>` somewhere at depth within a
   type, after instantiating and substituting a polymorphic type scheme).

   The `resolve*` functions, below, normalize a type to only contain monomorphic
   type names (and no more type applications). For the first use-case, we
   allocate names on the fly, but not for the second. *)
let resolve mem t: typ =
  match t with
  | TApp _ | TCgApp _ when mem (flatten_tapp t) ->
      TQualified (snd (Hashtbl.find state (flatten_tapp t)))
  | TTuple ts when mem (tuple_lid, ts, []) ->
      TQualified (snd (Hashtbl.find state (tuple_lid, ts, [])))
  | _ ->
      t

let resolve_deep mem = (object(self)
  inherit [_] map

  method! visit_TBuf () t c =
    match t with
    | TApp ((["Eurydice"], "derefed_slice"), [ t ]) ->
        (* TBuf (TApp ...) ~~> TApp *)
        let t = self#visit_typ () t in
        let lid = ["Eurydice"], if c then "dst_ref_shared" else "dst_ref_mut" in
        resolve mem (TApp (lid, [t; Helpers.usize]))
    | _ ->
        TBuf (self#visit_typ () t, c)

  method! visit_TApp () t ts =
    let ts = List.map (self#visit_typ ()) ts in
    resolve mem (TApp (t, ts))

  method! visit_TCgApp () t ts =
    resolve mem (TCgApp (t, ts))

  method! visit_TTuple () ts =
    let ts = List.map (self#visit_typ ()) ts in
    resolve mem (TTuple ts)
end)#visit_typ ()

let normalize = resolve_deep (Hashtbl.mem state)


(** Monomorphization of functions *********************************************)
type reverse_mapping = (lident * expr list * typ list, lident) Hashtbl.t

let generated_lids: reverse_mapping = Hashtbl.create 41

let debug () =
  Hashtbl.iter (fun (lid, ts, cgs) (_, monomorphized_lid) ->
    KPrint.bprintf "%a <%a> <%a> ~~> %a\n" plid lid pcgs cgs ptyps ts plid monomorphized_lid
  ) state;
  Hashtbl.iter (fun (lid, es, ts) monomorphized_lid ->
    KPrint.bprintf "%a <%a> <%a> ~~> %a\n" plid lid pexprs es ptyps ts plid
    monomorphized_lid
  ) generated_lids
