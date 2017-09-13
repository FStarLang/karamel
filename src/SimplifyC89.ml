(* A set of transformations for the sole purpose of bringing us closer to C89
 * compatibility. *)

open Ast
open Helpers

let hoist_lets = object (self)

  inherit [_] map

  method private scope_start t e =
    let env = ref [] in
    let e = self#visit env e in
    let bs = List.rev_map (fun b ->
      mark_mut b, any
    ) !env in
    nest bs t e

  method! dfunction _ cc flags n ret name binders body =
    let body = self#scope_start ret body in
    DFunction (cc, flags, n, ret, name, binders, body)

  method! elet env t b e1 e2 =
    match e1.node with
    | EPushFrame ->
        ELet (sequence_binding (),
          with_unit EPushFrame,
          DeBruijn.lift 1 (self#scope_start t e2))
    | _ when b.node.meta = Some MetaSequence ->
        ELet (b, self#visit env e1, self#visit env e2)
    | _ ->
        let b, e2 = DeBruijn.open_binder b e2 in
        env := b :: !env;
        let e1 = self#visit env e1 in
        let e2 = self#visit env e2 in
        ELet (sequence_binding (),
          with_unit (EAssign (with_type b.typ (EOpen (b.node.name, b.node.atom)), e1)),
          DeBruijn.lift 1 e2)
end

let simplify (files: file list): file list =
  let files = visit_files () Simplify.sequence_to_let files in
  let files = visit_files (ref []) hoist_lets files in
  let files = visit_files () Simplify.let_to_sequence files in
  files
