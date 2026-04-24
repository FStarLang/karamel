(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Transform functions with early returns to use goto. When activated via
    -goto_for_early_return, any function whose body contains a return statement
    in non-tail position is rewritten so that:
    - a return variable is allocated at the top (for non-void functions),
    - every return is replaced by an assignment + goto,
    - a label and final return are appended at the end.

    This pass operates on the CStar AST, before lowering to C11. *)

open CStar

(* Position-aware early-return detection. A return in "terminal" position
   (i.e., last statement in the function body, or in a branch of an
   if-then-else/switch that is itself in terminal position) is NOT early.
   Any return in non-terminal position IS early. *)
let has_early_return (body: block): bool =
  let found = ref false in
  (* Walk statements. [terminal] tracks whether the current position could
     be the "last thing" before the function returns naturally. *)
  let rec walk_block ~terminal (stmts: block) =
    match stmts with
    | [] -> ()
    | [s] -> walk_stmt ~terminal s
    | s :: rest -> walk_stmt ~terminal:false s; walk_block ~terminal rest
  and walk_stmt ~terminal (s: stmt) =
    match s with
    | Return _ ->
        if not terminal then found := true
    | IfThenElse (_, _, b1, b2) ->
        walk_block ~terminal b1;
        walk_block ~terminal b2
    | Switch (_, branches, default) ->
        List.iter (fun (_, b) -> walk_block ~terminal b) branches;
        Option.iter (walk_block ~terminal) default
    | While (_, b) ->
        (* Loop body is not terminal — the loop may exit without returning *)
        walk_block ~terminal:false b
    | For (_, _, _, b) ->
        walk_block ~terminal:false b
    | Block b ->
        walk_block ~terminal b
    | Abort _ | Break | Continue | Comment _ | Goto _ | Label _
    | Ignore _ | Decl _ | Assign _ | BufWrite _ | BufBlit _ | BufFill _
    | BufFree _ ->
        ()
  in
  walk_block ~terminal:true body;
  !found

(* Generate a type-specific zero initializer expression for the return
   variable. *)
let zero_initializer (t: typ): expr =
  match t with
  | Int w -> Constant (w, "0")
  | Bool -> Bool false
  | Pointer _ -> BufNull
  | Void -> failwith "zero_initializer called on Void"
  | Qualified _ | Struct _ | Enum _ | Union _ | Array _ | Function _
  | Const _ ->
      (* For aggregate/named types, produce a struct literal with a single
         zero field. CStarToC11 translates this to { 0U }. *)
      Struct (None, [(None, Constant (Constant.UInt8, "0"))])

(* Rewrite a block, replacing Return statements with assignment + goto. *)
let rewrite_block (ret_var: ident) (ret_typ: typ) (label: ident) (is_void: bool) (body: block): block =
  let rec rewrite_stmts (stmts: block): block =
    List.concat_map rewrite_one stmts
  and rewrite_one (s: stmt): block =
    match s with
    | Return (Some e) when not is_void ->
        [Assign (Var ret_var, ret_typ, e); Goto label]
    | Return (Some _e) when is_void ->
        Warn.fatal_error "void function returning a value"
    | Return None ->
        [Goto label]
    | IfThenElse (ifdef, e, b1, b2) ->
        [IfThenElse (ifdef, e, rewrite_stmts b1, rewrite_stmts b2)]
    | Switch (e, branches, default) ->
        [Switch (e,
          List.map (fun (c, b) -> (c, rewrite_stmts b)) branches,
          Option.map rewrite_stmts default)]
    | While (e, b) ->
        [While (e, rewrite_stmts b)]
    | For (init, e, iter, b) ->
        [For (init, e, iter, rewrite_stmts b)]
    | Block b ->
        [Block (rewrite_stmts b)]
    | s -> [s]
  in
  rewrite_stmts body

(* Rewrite a single CStar declaration if it has early returns. *)
let rewrite_decl (d: decl): decl =
  match d with
  | Function (cc, flags, ret_typ, lid, binders, body) when has_early_return body ->
      let is_void = (ret_typ = Void) in
      let used = names_of_block body in
      let is_used n = S.mem n used in
      let ret_var = Idents.mk_fresh "result" is_used in
      let label = Idents.mk_fresh "exit" is_used in
      let rewritten = rewrite_block ret_var ret_typ label is_void body in
      let new_body =
        if is_void then
          rewritten @ [Label label]
        else
          let init = zero_initializer ret_typ in
          [Decl ({ name = ret_var; typ = ret_typ }, init)]
          @ rewritten
          @ [Label label; Return (Some (Var ret_var))]
      in
      Function (cc, flags, ret_typ, lid, binders, new_body)
  | d -> d

let rewrite_file (decls: decl list): decl list =
  List.map rewrite_decl decls
