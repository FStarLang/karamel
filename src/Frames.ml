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
open Simplify
open Warnings

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

let inline_analysis files =
  let lookup lid =
    let module L = struct exception Found of (typ * lident * binder list * expr) end in
    try
      ignore (visit_files () (object
        inherit [_] map as super
        method dfunction () ret name binders body =
          if name = lid then
            raise (L.Found (ret, name, binders, body))
          else
            super#dfunction () ret name binders body
      end) files);
      raise Not_found
    with L.Found def ->
      def
  in

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
      let _ret_type, _, _binders, body = lookup lid in
      walk Safe body
    with Not_found ->
      (* Reference to an undefined, external function *)
      MustInline
  in

  F.lfp must_inline

let debug files =
  let valuation = inline_analysis files in
  List.iter (fun (_, program) ->
    List.iter (function
      | DFunction (_, name, _, _) ->
          if valuation name = MustInline then
            KPrint.bprintf "%a must be inlined\n" plid name
      | _ ->
          ()
    ) program
  ) files
