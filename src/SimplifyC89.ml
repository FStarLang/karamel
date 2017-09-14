(* A set of transformations for the sole purpose of bringing us closer to C89
 * compatibility. *)

open Ast
open Helpers

(* This phase precedes [hoist_bufcreate] and relies on [hoist]. It differs in
 * that the notion of scope is just the C scope (it's a cosmetic criterion)
 * whereas hoisting EBufCreate's requires a semantic notion that's encoded by
 * the EPushFrame marker. *)
let hoist_lets = object (self)

  inherit [_] map

  method private scope_start t e =
    match e.node with
    | ELet (b, e1, e2) when b.node.meta <> Some MetaSequence ->
        (* No ELet's in e1 so nothing to hoist *)
        with_type t (ELet (b, e1, self#scope_start t e2))
    | _ ->
        let env = ref [] in
        let e = self#visit env e in
        let bs = List.rev_map (fun b ->
          mark_mut b, any
        ) !env in
        nest bs t e

  method! dfunction _ cc flags n ret name binders body =
    let body = self#scope_start ret body in
    DFunction (cc, flags, n, ret, name, binders, body)

  method! eifthenelse _ t e1 e2 e3 =
    (* No ELet's in e1 *)
    EIfThenElse (e1, self#scope_start t e2, self#scope_start t e3)

  method! efor _ _ b e1 e2 e3 e4 =
    EFor (b, e1, e2, e3, self#scope_start TUnit e4)

  method! elet env t b e1 e2 =
    match e1.node with
    | EPushFrame ->
        ELet (sequence_binding (),
          with_unit EPushFrame,
          DeBruijn.lift 1 (self#scope_start t e2))

    | _ when b.node.meta = Some MetaSequence ->
        let e1 = self#visit env e1 in
        let e2 = self#visit env e2 in
        ELet (b, e1, e2)

    | _ ->
        match strengthen_array' b.typ e1 with
        | Some typ ->
            let b, e2 = DeBruijn.open_binder b e2 in
            let b = { b with typ } in
            env := b :: !env;
            let e1 = self#visit env e1 in
            let e2 = self#visit env e2 in
            ELet (sequence_binding (),
              with_unit (EAssign (with_type b.typ (EOpen (b.node.name, b.node.atom)), e1)),
              DeBruijn.lift 1 e2)
        | None ->
            (* Might be salvageable by hoist_buf *)
            let e1 = self#visit env e1 in
            let e2 = self#visit env e2 in
            ELet (b, e1, e2)
end
