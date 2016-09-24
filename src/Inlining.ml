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
open Idents

let plid = PrintAst.plid
let pexpr = PrintAst.pexpr

module LidMap = Map.Make(struct
  type t = lident
  let compare = compare
end)

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
  let lookup lid = snd (Hashtbl.find map lid) in
  let debug_inline = false in

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
      | _ ->
          contains_alloc valuation e
    in
    try
      let body = lookup lid in
      if walk body then
        MustInline
      else
        Safe
    with Not_found ->
      (* Reference to an undefined, external function. This is sound only if
       * externally-realized functions execute in their own stack frame, which
       * is fine, because they actually are, well, functions written in C. *)
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

let inline_function_frames files =
  (* A stateful graph traversal that uses the textbook three colors to rule out
   * cycles. *)
  let map = build_map files (fun map -> function
    | DFunction (_, name, _, body) -> Hashtbl.add map name (White, body)
    | _ -> ()
  ) in
  let valuation = inline_analysis map in

  (* Because we want to recursively, lazily evaluate the inlining of each
   * function, we temporarily store the bodies of each function in a mutable map
   * and inline them as we hit them. *)
  let inline_one = memoize_inline map (fun recurse -> (object(self)
    inherit [unit] map
    method eapp () _ e es =
      let es = List.map (self#visit ()) es in
      match e.node with
      | EQualified lid when valuation lid = MustInline && Hashtbl.mem map lid ->
          (DeBruijn.subst_n (recurse lid) es).node
      | _ ->
          EApp (self#visit () e, es)
    method equalified () t lid =
      match t with
      | TArrow _ when valuation lid = MustInline && Hashtbl.mem map lid ->
          fatal_error "[Frames]: partially applied function; not meant to happen";
      | _ ->
          EQualified lid
  end)#visit ()) in

  (* This is where the evaluation of the inlining is forced: every function that
   * must be inlined is dropped (otherwise the C compiler is not going to be
   * very happy if it sees someone returning a stack pointer!); functions that
   * are meant to be kept are run through [inline_one]. *)
  filter_decls (function
    | DFunction (ret, name, binders, _) ->
        if valuation name = MustInline && string_of_lident name <> "main" then
          None
        else
          Some (DFunction (ret, name, binders, inline_one name))
    | d ->
        Some d
  ) files


let inline_type_abbrevs files =
  let map = build_map files (fun map -> function
    | DTypeAlias (lid, _, t) -> Hashtbl.add map lid (White, t)
    | _ -> ()
  ) in

  let inliner inline_one = object
    inherit [unit] map
    method tapp () lid' ts =
      if not (Hashtbl.mem map lid') then begin
        TAny
      end else
        DeBruijn.subst_tn (inline_one lid') ts
  end in

  let inline_one = memoize_inline map (fun recurse -> (inliner recurse)#visit_t ()) in

  let files = filter_decls (function
    | DTypeAlias (lid, n, _) ->
        if n = 0 then
          Some (DTypeAlias (lid, n, inline_one lid))
        else
          None
    | d ->
        Some d
  ) files in
  Simplify.visit_files () (inliner inline_one) files
