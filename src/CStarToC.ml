(** Converting from C* to C abstract syntax. *)

open C
open CStar

let string_of_lident (idents, ident) =
  if List.length idents > 0 then
    String.concat "_" idents ^ "_" ^ ident
  else
    ident

(* Turns the ML declaration inside-out to match the C reading of a type. *)
let mk_spec_and_declarator, mk_spec_and_declarator_f =
  let rec mk name (t: typ) (k: C.declarator -> C.declarator): C.type_spec * C.declarator =
    match t with
    | Pointer t ->
        mk name t (fun d -> Pointer (k d))
    | Array (t, size) ->
        mk name t (fun d -> Array (k d, size))
    | Function (t, ts) ->
        mk name t (fun d -> Function (k d, List.map (fun t -> mk "" t (fun d -> d)) ts))
    | Int w ->
        Int w, k (Ident name)
    | Void ->
        Void, k (Ident name)
    | Named n ->
        Named n, k (Ident name)
  in
  (fun name t ->
    mk name t (fun d -> d)),
  (fun name ret_t params ->
    mk name ret_t (fun d -> Function (d, List.map (fun (n, t) -> mk n t (fun d -> d)) params)))

(* Enforce the invariant that declarations are wrapped in compound statements
 * and cannot appear "alone". *)
let mk_compound_if (stmts: C.stmt list): C.stmt =
  match stmts with
  | [ Decl _ ] ->
      Compound stmts
  | [ stmt ] ->
      stmt
  | _ ->
      Compound stmts

let ensure_compound (stmts: C.stmt list): C.stmt =
  match stmts with
  | [ Compound _ as stmt ] ->
      stmt
  | _ ->
      Compound stmts

let rec mk_stmt (stmt: stmt): C.stmt =
  match stmt with
  | Return e ->
      Return (Some (mk_expr e))

  | Ignore e ->
      Expr (mk_expr e)

  | Decl (binder, BufCreate (size, init)) ->
      (* In the case where this is a buffer creation in the C* meaning, then we
       * declare a fixed-length array; this is an "upcast" from pointer type to
       * array type, in the C sense. *)
      let size = match size with
        | Constant k -> k
        | _ -> failwith "[mk_stmt]: non constant-size arrays not supported"
      in
      let t = match binder.typ with
        | Pointer t -> Array (t, size)
        | _ -> failwith "impossible"
      in
      let init: C.init = match init with
        | Constant ((_, "0") as k) -> Initializer [ Expr (C.Constant k) ]
        | _ -> failwith "[mk_stmt]: non zero-initialized arrays not supported"
      in
      let spec, decl = mk_spec_and_declarator binder.name t in
      Decl (spec, None, [ decl, Some init ])

  | Decl (binder, e) ->
      let spec, decl = mk_spec_and_declarator binder.name binder.typ in
      let e = mk_expr e in
      Decl (spec, None, [ decl, Some (Expr e) ])

  | IfThenElse (e, b1, b2) ->
      if List.length b2 > 0 then
        SelectIfElse (mk_expr e, mk_compound_if (mk_stmts b1), mk_compound_if (mk_stmts b2))
      else
        SelectIf (mk_expr e, mk_compound_if (mk_stmts b1))

  | Assign (e1, e2) ->
      Expr (Assign (mk_expr e1, mk_expr e2))

  | BufWrite (e1, e2, e3) ->
      Expr (Assign (Index (mk_expr e1, mk_expr e2), mk_expr e3))

and mk_stmts stmts =
  List.map mk_stmt stmts

and mk_expr (e: expr): C.expr =
  match e with
  | Call (Op o, [ e ]) ->
      Op1 (o, mk_expr e)

  | Call (Op o, [ e1; e2 ]) ->
      Op2 (o, mk_expr e1, mk_expr e2)

  | Call (e, es) ->
      Call (mk_expr e, List.map mk_expr es)

  | Var ident ->
      Name ident

  | Qualified lident ->
      Name (string_of_lident lident)

  | Constant k ->
      Constant k

  | BufCreate _ ->
      failwith "[mk_expr]: Buffer.create may only appear as let ... = Buffer.create"

  | BufRead (e1, e2) ->
      Index (mk_expr e1, mk_expr e2)

  | BufSub (e1, e2) ->
      Op2 (K.Add, mk_expr e1, mk_expr e2)

  | Cast (e, t) ->
      Cast (mk_type t, mk_expr e)

  | Op _ ->
      failwith "[mk_expr]: impossible, should've caught it earlier..."


and mk_type t =
  (* hack alert *)
  mk_spec_and_declarator "" t
  
let mk_decl_or_function (d: decl): C.declaration_or_function =
  match d with
  | TypeAlias (name, t) ->
      let spec, decl = mk_spec_and_declarator name t in
      Decl (spec, Some Typedef, [ decl, None ])

  | Function (return_type, name, parameters, body) ->
      let parameters = List.map (fun { name; typ } -> name, typ) parameters in
      let spec, decl = mk_spec_and_declarator_f name return_type parameters in
      let body = ensure_compound (mk_stmts body) in
      Function ((spec, None, [ decl, None ]), body)

let mk_program decls =
  List.map mk_decl_or_function decls

let mk_files files =
  List.map (fun (name, program) -> name, mk_program program) files
