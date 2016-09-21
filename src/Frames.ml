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

let build_map files =
  let map = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (function
      | DFunction (_, name, _, body) ->
          Hashtbl.add map name (White, body)
      | _ ->
          ()
    ) decls
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

let inline_as_required files =
  (* A stateful graph traversal that uses the textbook three colors to rule out
   * cycles. *)
  let map = build_map files in
  let valuation = inline_analysis map in

  (* Because we want to recursively, lazily evaluate the inlining of each
   * function, we temporarily store the bodies of each function in a mutable map
   * and inline them as we hit them. *)
  let rec inline_one lid =
    let color, body = Hashtbl.find map lid in
    match color with
    | Gray ->
        fatal_error "[Frames]: cyclic dependency on %a" plid lid
    | Black ->
        body
    | White ->
        Hashtbl.add map lid (Gray, { node = EAny; mtyp = TAny });
        let body = (object(self)
          inherit [unit] map
          method eapp () _ e es =
            let es = List.map (self#visit ()) es in
            match e.node with
            | EQualified lid when valuation lid = MustInline && Hashtbl.mem map lid ->
                let l = List.length es in
                (KList.fold_lefti (fun i body arg ->
                  let k = l - i - 1 in
                  DeBruijn.subst arg k body
                ) (inline_one lid) es).node
            | _ ->
                EApp (self#visit () e, es)
          method equalified () t lid =
            match t with
            | TArrow _ when valuation lid = MustInline && Hashtbl.mem map lid ->
                fatal_error "[Frames]: partially applied function; not meant to happen";
            | _ ->
                EQualified lid
        end)#visit () body in
        Hashtbl.add map lid (Black, body);
        body
  in

  (* This is where the evaluation of the inlining is forced: every function that
   * must be inlined is dropped (otherwise the C compiler is not going to be
   * very happy if it sees someone returning a stack pointer!); functions that
   * are meant to be kept are run through [inline_one]. *)
  List.map (fun (file, decls) ->
    file, KList.filter_map (function
      | DFunction (ret, name, binders, _) ->
          if valuation name = MustInline && string_of_lident name <> "main" then
            None
          else
            Some (DFunction (ret, name, binders, inline_one name))
      | d ->
          Some d
    ) decls
  ) files
