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
let ( ||| ) = lub

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

  (** To determine whether a function should be inlined, we use a syntactic
   * criterion: any buffer allocation that happens before a [push_frame] implies
   * the function must be inlined to be sound. Any reference to an external
   * function also is enough of a reason to inline. *)
  (** TODO: this criterion is not sound as it stands because we should also
   * check what happens _after_ the EPopFrame. *)
  let contains_alloc valuation expr =
    let module L = struct exception Found end in
    try
      ignore ((object
        inherit [_] map as super
        method! ebufcreate () _ _ _ =
          raise L.Found
        method! ebufcreatel () _ _ =
          raise L.Found
        method! equalified () t lid =
          (* In case we ever decide to allow wacky stuff like:
           *   let f = if ... then g else h in
           *   ignore f;
           * then this will become an over-approximation. *)
          if valuation lid = MustInline then
            raise L.Found
          else
            super#equalified () t lid
      end)#visit () expr);
      Safe
    with L.Found ->
      MustInline
  in

  let must_inline lid valuation =
    let rec walk found e =
      match e.node with
      | ELet (_, body, cont) ->
          walk (found ||| contains_alloc valuation body) cont
      | ESequence es ->
          let rec walk found = function
            | { node = EPushFrame; _ } :: _ ->
                found
            | e :: es ->
                walk (found ||| contains_alloc valuation e) es
            | [] ->
                found
          in
          walk found es
      | EPushFrame ->
          fatal_error "Malformed function body %a" plid lid
      | _ ->
          found ||| contains_alloc valuation e
    in
    try
      let body = lookup lid in
      walk Safe body
    with Not_found ->
      (* Reference to an undefined, external function *)
      MustInline
  in

  F.lfp must_inline

let inline_as_required files =
  (* A stateful graph traversal that uses the textbook three colors to rule out
   * cycles. *)
  let map = build_map files in
  let valuation = inline_analysis map in

  let debug () =
    Hashtbl.iter (fun lid _ ->
      if valuation lid = MustInline then
        KPrint.bprintf "%a will be inlined\n" plid lid
    ) map;
  in
  if false then debug ();

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
                (List.fold_right (fun arg body ->
                  DeBruijn.subst arg 0 body
                ) es (inline_one lid)).node
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
          if valuation name = MustInline && string_of_lident main <> "main" then
            None
          else
            Some (DFunction (ret, name, binders, inline_one name))
      | d ->
          Some d
    ) decls
  ) files
