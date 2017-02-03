(** Make sure the notion of Low* frames is soundly implemented in C*. In
 * particular, if a function doesn't push/pop a frame _and_ allocates, then it
 * originates from the [StackInline] or [Inline] effects and must be inlined so
 * as to perform allocations in its parent frame. *)

(** We perform a fixpoint computation on the following simple lattice:

    mustinline
      |
    safe

 * This is a whole-program analysis.
*)

open Ast
open Warnings
open PrintAst.Ops
open Common

module LidMap = Idents.LidMap

module ILidMap = struct
  type key = lident
  type 'data t = 'data LidMap.t ref
  let create () = ref LidMap.empty
  let clear m = m := LidMap.empty
  let add k v m = m := LidMap.add k v !m
  let find k m = LidMap.find k !m
  let iter f m = LidMap.iter f !m
end

type property = Safe | MustInline

let lub x y =
  match x, y with
  | Safe, Safe -> Safe
  | _ -> MustInline

module Property = struct
  type nonrec property = property
  let bottom = Safe
  let equal = (=)
  let is_maximal p = p = MustInline
end

module F = Fix.Make(ILidMap)(Property)

type color = White | Gray | Black

(** Build an empty map for an inlining traversal, where [f] is responsible for
 * filling the initial values with the pair [(White, initial_body)]. *)
let build_map files f =
  let map = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (f map) decls
  ) files;
  map

let inline_analysis map =
  let lookup lid = Hashtbl.find map lid in
  let debug_inline = Options.debug "inline" in

  (** To determine whether a function should be inlined, we use a syntactic
   * criterion: any buffer allocation that happens before a [push_frame] implies
   * the function must be inlined to be sound. Any reference to an external
   * function also is enough of a reason to inline. *)
  (** TODO: this criterion is not sound as it stands because we should also
   * check what happens _after_ the EPopFrame. *)
  let contains_alloc lid valuation expr =
    let module L = struct exception Found of string end in
    try
      ignore ((object
        inherit [_] map as super
        method! ebufcreate () _ _ _ =
          raise (L.Found "bufcreate")
        method! ebufcreatel () _ _ =
          raise (L.Found "bufcreateL")
        method! equalified () t lid =
          (* In case we ever decide to allow wacky stuff like:
           *   let f = if ... then g else h in
           *   ignore f;
           * then this will become an over-approximation. *)
          match t with
          | TArrow _ when valuation lid = MustInline ->
              raise (L.Found (KPrint.bsprintf "transitive: %a" plid lid))
          | _ ->
              super#equalified () t lid
      end)#visit () expr);
      false
    with L.Found reason ->
      if debug_inline then
        KPrint.bprintf "%a will be inlined because: %s\n" plid lid reason;
      true
  in

  let must_inline lid valuation =
    let contains_alloc = contains_alloc lid in
    let rec walk e =
      match e.node with
      | ELet (_, body, cont) ->
          contains_alloc valuation body || walk cont
      | ESequence es ->
          let rec walk = function
            | { node = EPushFrame; _ } :: _ ->
                false
            | e :: es ->
                contains_alloc valuation e || walk es
            | [] ->
                false
          in
          walk es
      | EPushFrame ->
          fatal_error "Malformed function body %a" plid lid
      | EIfThenElse (e1, e2, e3) ->
          contains_alloc valuation e1 ||
          walk e2 ||
          walk e3
      | ESwitch (e, branches) ->
          contains_alloc valuation e ||
          List.exists (fun (_, e) ->
            walk e
          ) branches
      | EMatch (e, branches) ->
          contains_alloc valuation e ||
          List.exists (fun (_, _, e) ->
            walk e
          ) branches
      | _ ->
          contains_alloc valuation e
    in
    match lookup lid with
    | exception Not_found ->
        (* Reference to an undefined, external function. This is sound only if
         * externally-realized functions execute in their own stack frame, which
         * is fine, because they actually are, well, functions written in C. *)
        Safe
    | body ->
        if walk body then begin
          MustInline
        end else
          Safe
  in

  F.lfp must_inline

(* A generic graph traversal + memoization combinator we use for inline
 * functions and types. *)
let rec memoize_inline map visit lid =
  let color, body = Hashtbl.find map lid in
  match color with
  | Gray ->
      fatal_error "[Frames]: cyclic dependency on %a" plid lid
  | Black ->
      body
  | White ->
      Hashtbl.add map lid (Gray, body);
      let body = visit (memoize_inline map visit) body in
      Hashtbl.add map lid (Black, body);
      body

let filter_decls f files =
  List.map (fun (file, decls) -> file, KList.filter_map f decls) files

let iter_decls f files =
  List.iter (fun (_, decls) -> List.iter f decls) files

(* Inline function bodies *****************************************************)

let inline_function_frames files =
  (* A stateful graph traversal that uses the textbook three colors to rule out
   * cycles. The first component is used ONLY by [inline_analysis], while the
   * color is used ONLY by [memoize_inline]. *)
  let map = build_map files (fun map -> function
    | DFunction (_, _, _, name, _, body) ->
        Hashtbl.add map name body
    | _ ->
        ()
  ) in
  let valuation = inline_analysis map in

  (* Because we want to recursively, lazily evaluate the inlining of each
   * function, we temporarily store the bodies of each function in a mutable map
   * and inline them as we hit them. *)
  let map = build_map files (fun map -> function
    | DFunction (_, _, _, name, _, body) ->
        Hashtbl.add map name (White, body)
    | _ ->
        ()
  ) in
  let inline_one = memoize_inline map (fun recurse -> (object(self)
    inherit [unit] map
    method eapp () t e es =
      let es = List.map (self#visit ()) es in
      match e.node with
      | EQualified lid when valuation lid = MustInline && Hashtbl.mem map lid ->
          (* We use a syntactic criterion to ensure that all the arguments are
           * values, i.e. can be safely substituted inside the function
           * definition. *)
          let bs, es = KList.fold_lefti (fun i (bs, es) e ->
            if not (is_value e) then
              let x, atom = Simplify.mk_binding (Printf.sprintf "x%d" i) e.typ in
              (x, e) :: bs, atom :: es
            else
              bs, e :: es
          ) ([], []) es in
          let bs = List.rev bs in
          let es = List.rev es in
          EComment (
            KPrint.bsprintf "start inlining %a" plid lid,
            Simplify.nest bs t (
              DeBruijn.subst_n (recurse lid) es),
            KPrint.bsprintf "end inlining %a" plid lid)
      | _ ->
          EApp (self#visit () e, es)
    method equalified () t lid =
      match t with
      | TArrow _ when valuation lid = MustInline && Hashtbl.mem map lid ->
          fatal_error "[Frames]: partially applied function; not meant to happen";
      | _ ->
          EQualified lid
  end)#visit ()) in

  let safely_private = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (function
      | DGlobal (flags, name, _, _)
      | DFunction (_, flags, _, name, _, _) ->
          if List.mem Private flags then
            Hashtbl.add safely_private name ()
      | _ ->
          ()
    ) decls
  ) files;

  (* Note that because of bundling, we no longer have the invariant that the
   * left-hand-side of an [lident] maps to the name of the file it originates
   * from. *)
  let file_of = Bundles.mk_file_of files in

  (* While we're at it, after inlining, we may drop some private qualifiers for
   * functions in other modules that end up being called. *)
  let unmark_private_in name body = 
    ignore ((object(self)
      inherit [unit] map
      method eapp () _ e es =
        match e.node with
        | EQualified name' ->
            (* There is a cross-compilation-unit call from [name] to
             * [name‘], meaning that the latter cannot safely remain
             * inline. *)
            if file_of name <> file_of name' && Hashtbl.mem safely_private name' then begin
              Warnings.maybe_fatal_error ("", LostStatic (name, name'));
              Hashtbl.remove safely_private name'
            end;
            EApp (e, List.map (self#visit ()) es)
        | _ ->
            EApp (self#visit () e, List.map (self#visit ()) es)
      method equalified () _ name' =
        if file_of name <> file_of name' && Hashtbl.mem safely_private name' then begin
          Warnings.maybe_fatal_error ("", LostStatic (name, name'));
          Hashtbl.remove safely_private name'
        end;
        EQualified name'
    end)#visit () body)
  in

  (* This is where the evaluation of the inlining is forced: every function that
   * must be inlined is dropped (otherwise the C compiler is not going to be
   * very happy if it sees someone returning a stack pointer!); functions that
   * are meant to be kept are run through [inline_one]. *)
  let files = filter_decls (function
    | DFunction (cc, flags, ret, name, binders, _) ->
        if valuation name = MustInline && Simplify.target_c_name name <> "main" then
          None
        else
          let body = inline_one name in
          unmark_private_in name body;
          Some (DFunction (cc, flags, ret, name, binders, body))
    | d ->
        (* Note: not inlining globals because F* should forbid top-level
         * effects...? *)
        Some d
  ) files in

  let keep_private_if name flags =
    if not (Hashtbl.mem safely_private name) || Simplify.target_c_name name = "main" then
      List.filter ((<>) Private) flags
    else
      flags
  in

  (* If after inlining, the function does not appear in [safely_private], then it
   * certainly cannot keep its flag. *)
  filter_decls (function
    | DFunction (cc, flags, ret, name, binders, body) ->
        Some (DFunction (cc, keep_private_if name flags, ret, name, binders, body))
    | DGlobal (flags, name, e, t) ->
        Some (DGlobal (keep_private_if name flags, name, e, t))
    | d ->
        Some d
  ) files



(* Monomorphize types *********************************************************)

let inline_type_abbrevs files =
  let map = build_map files (fun map -> function
    | DType (lid, _, Abbrev t) -> Hashtbl.add map lid (White, t)
    | _ -> ()
  ) in

  let inliner inline_one = object(self)
    inherit [unit] map
    method tapp () lid ts =
      try DeBruijn.subst_tn (inline_one lid) ts
      with Not_found -> TApp (lid, List.map (self#visit_t ()) ts)
    method tqualified () lid =
      try inline_one lid
      with Not_found -> TQualified lid
  end in

  let inline_one = memoize_inline map (fun recurse -> (inliner recurse)#visit_t ()) in

  Simplify.visit_files () (inliner inline_one) files


let drop_type_abbrevs files =
  let files = Simplify.visit_files () (object
    inherit [unit] map
    method tapp _ _ _ =
      TAny
  end) files in
  filter_decls (function
    | DType (lid, n, Abbrev def) ->
        if n = 0 then
          Some (DType (lid, n, Abbrev def))
        else
          (* A type definition with parameters is not something we'll be able to
           * generate code for (at the moment). So, drop it. *)
          None
    | d ->
        Some d
  ) files


(* Drop unused private functions **********************************************)

let drop_unused files =
  let visited = Hashtbl.create 41 in
  let must_keep = Hashtbl.create 41 in
  let body_of_lid = build_map files (fun map -> function
    | DFunction (_, _, _, name, _, body)
    | DGlobal (_, name, _, body) ->
        Hashtbl.add map name body
    | _ ->
        ()
  ) in
  let rec visit lid =
    if Hashtbl.mem visited lid then
      ()
    else begin
      Hashtbl.add visited lid ();
      Hashtbl.add must_keep lid ();
      match Hashtbl.find body_of_lid lid with
      | exception Not_found -> ()
      | body -> visit_e body
    end
  and visit_e body =
    ignore ((object
      inherit [_] map
      method equalified () _ lid =
        visit lid;
        EQualified lid
    end)#visit () body)
  in
  iter_decls (function
    | DFunction (_, flags, _, lid, _, body)
    | DGlobal (flags, lid, _, body) ->
        if (not (List.exists ((=) Private) flags)) then begin
          Hashtbl.add must_keep lid ();
          visit_e body
        end;
    | _ ->
        ()
  ) files;
  filter_decls (fun d ->
    match d with
    | DGlobal (flags, lid, _, _)
    | DFunction (_, flags, _, lid, _, _) ->
        if not (Hashtbl.mem must_keep lid) then begin
          assert (List.exists ((=) Private) flags);
          None
        end else
          Some d
    | d ->
        Some d
  ) files
