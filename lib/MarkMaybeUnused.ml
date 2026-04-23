(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Mark hoisted local variable declarations as maybe_unused when they appear
    before #if/#ifdef blocks and are not referenced in all branches. *)

module C = C11
module SSet = Set.Make(String)

(* Collect all variable names referenced in a C11 expression. *)
let rec vars_of_expr (e: C.expr): SSet.t =
  match e with
  | C.Name n -> SSet.singleton n
  | C.Op1 (_, e) -> vars_of_expr e
  | C.Op2 (_, e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | C.Index (e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | C.Deref e -> vars_of_expr e
  | C.Address e -> vars_of_expr e
  | C.Member (e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | C.MemberP (e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | C.Assign (e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | C.Call (e, es) ->
      List.fold_left (fun acc e -> SSet.union acc (vars_of_expr e))
        (vars_of_expr e) es
  | C.Cast (_, e) -> vars_of_expr e
  | C.Literal _ | C.Constant _ | C.Bool _ -> SSet.empty
  | C.Sizeof e -> vars_of_expr e
  | C.CompoundLiteral (_, inits) -> vars_of_inits inits
  | C.MemberAccess (e, _) -> vars_of_expr e
  | C.MemberAccessPointer (e, _) -> vars_of_expr e
  | C.InlineComment (_, e, _) -> vars_of_expr e
  | C.Type _ -> SSet.empty
  | C.Stmt stmts -> vars_of_stmts stmts
  | C.CxxInitializerList init -> vars_of_init init

and vars_of_init (i: C.init): SSet.t =
  match i with
  | C.InitExpr e -> vars_of_expr e
  | C.Designated (_, i) -> vars_of_init i
  | C.Initializer is -> vars_of_inits is

and vars_of_inits (is: C.init list): SSet.t =
  List.fold_left (fun acc i -> SSet.union acc (vars_of_init i)) SSet.empty is

(* Collect all variable names referenced in a list of statements. *)
and vars_of_stmts (stmts: C.stmt list): SSet.t =
  List.fold_left (fun acc s -> SSet.union acc (vars_of_stmt s)) SSet.empty stmts

and vars_of_stmt (s: C.stmt): SSet.t =
  match s with
  | Compound stmts -> vars_of_stmts stmts
  | Decl (_, _, _, _, _, decl_inits) ->
      List.fold_left (fun acc (_, _, init) ->
        match init with
        | Some i -> SSet.union acc (vars_of_init i)
        | None -> acc
      ) SSet.empty decl_inits
  | Expr e -> vars_of_expr e
  | If (e, s) -> SSet.union (vars_of_expr e) (vars_of_stmt s)
  | IfElse (e, s1, s2) ->
      SSet.union (vars_of_expr e)
        (SSet.union (vars_of_stmt s1) (vars_of_stmt s2))
  | IfDef (e, ss1, elifs, ss2) ->
      let acc = vars_of_expr e in
      let acc = SSet.union acc (vars_of_stmts ss1) in
      let acc = List.fold_left (fun acc (e, ss) ->
        SSet.union acc (SSet.union (vars_of_expr e) (vars_of_stmts ss))
      ) acc elifs in
      SSet.union acc (vars_of_stmts ss2)
  | While (e, s) -> SSet.union (vars_of_expr e) (vars_of_stmt s)
  | For (de, e1, e2, s) ->
      let acc = match de with
        | `Decl d -> vars_of_decl d
        | `Expr e -> vars_of_expr e
        | `Skip -> SSet.empty
      in
      SSet.union acc
        (SSet.union (vars_of_expr e1)
          (SSet.union (vars_of_expr e2) (vars_of_stmt s)))
  | Return (Some e) -> vars_of_expr e
  | Return None | Break | Continue -> SSet.empty
  | Switch (e, cases, default) ->
      let acc = vars_of_expr e in
      let acc = List.fold_left (fun acc (_, s) ->
        SSet.union acc (vars_of_stmt s)
      ) acc cases in
      SSet.union acc (vars_of_stmt default)
  | Comment _ -> SSet.empty

and vars_of_decl ((_, _, _, _, _, decl_inits): C.declaration): SSet.t =
  List.fold_left (fun acc (_, _, init) ->
    match init with
    | Some i -> SSet.union acc (vars_of_init i)
    | None -> acc
  ) SSet.empty decl_inits

(* Extract the declared variable name from a declarator. *)
let rec name_of_declarator (d: C.declarator): string option =
  match d with
  | C.Ident n -> Some n
  | C.Pointer (_, d) -> name_of_declarator d
  | C.Array (_, d, _) -> name_of_declarator d
  | C.Function (_, d, _) -> name_of_declarator d

(* Collect the intersection of variables referenced across all branches of an
   IfDef — i.e., variables that appear in EVERY branch. *)
let ifdef_common_vars (ss1: C.stmt list) (elifs: (C.expr * C.stmt list) list) (ss2: C.stmt list): SSet.t =
  let branch_vars = vars_of_stmts ss1 in
  let branch_vars =
    List.fold_left (fun acc (_, ss) ->
      SSet.inter acc (vars_of_stmts ss)
    ) branch_vars elifs
  in
  if ss2 = [] then
    branch_vars
  else
    SSet.inter branch_vars (vars_of_stmts ss2)

(* Given a statement list (function body), insert KRML_MAYBE_UNUSED_VAR calls
   inside each branch of an IfDef for variables that branch does not use. *)
let mark_maybe_unused_in_body (stmts: C.stmt list): C.stmt list =
  (* Collect declared variable names at function top *)
  let declared_vars =
    List.fold_left (fun acc (s: C.stmt) ->
      match s with
      | Decl (_, _, _, _, _, decl_inits) ->
          List.fold_left (fun acc (d, _, _) ->
            match name_of_declarator d with
            | Some n -> SSet.add n acc
            | None -> acc
          ) acc decl_inits
      | _ -> acc
    ) SSet.empty stmts
  in
  if SSet.is_empty declared_vars then
    stmts
  else
    let mk_unused_stmts vars =
      SSet.fold (fun n acc ->
        (C.Expr (C.Call (C.Name "KRML_MAYBE_UNUSED_VAR", [C.Name n])) : C.stmt) :: acc
      ) vars []
    in
    let mark_branch (branch_vars: SSet.t) (ss: C.stmt list): C.stmt list =
      let unused = SSet.diff declared_vars branch_vars in
      (* Only mark variables that are declared and unused in this branch *)
      let to_mark = SSet.inter unused declared_vars in
      if SSet.is_empty to_mark then ss
      else mk_unused_stmts to_mark @ ss
    in
    List.map (fun (s: C.stmt) ->
      match s with
      | IfDef (e, ss1, elifs, ss2) ->
          let all_branches_vars =
            let v = vars_of_stmts ss1 in
            let v = List.fold_left (fun acc (_, ss) ->
              SSet.union acc (vars_of_stmts ss)
            ) v elifs in
            SSet.union v (vars_of_stmts ss2)
          in
          let common = ifdef_common_vars ss1 elifs ss2 in
          let maybe_unused = SSet.inter declared_vars (SSet.diff all_branches_vars common) in
          if SSet.is_empty maybe_unused then s
          else
            let vars1 = vars_of_stmts ss1 in
            let ss1' = mark_branch vars1 ss1 in
            let elifs' = List.map (fun (e, ss) ->
              let vars = vars_of_stmts ss in
              (e, mark_branch vars ss)
            ) elifs in
            let ss2' = if ss2 = [] then ss2
              else
                let vars2 = vars_of_stmts ss2 in
                mark_branch vars2 ss2
            in
            (IfDef (e, ss1', elifs', ss2') : C.stmt)
      | other -> other
    ) stmts

let mark_maybe_unused_stmts (s: C.stmt): C.stmt =
  match s with
  | Compound stmts -> Compound (mark_maybe_unused_in_body stmts)
  | _ -> s

let mark_maybe_unused_files (files: (string * C.program) list): (string * C.program) list =
  List.map (fun (name, program) ->
    let program = List.map (fun (df: C.declaration_or_function) ->
      match df with
      | Function (comments, decl, body) ->
          (Function (comments, decl, mark_maybe_unused_stmts body) : C.declaration_or_function)
      | other -> other
    ) program in
    (name, program)
  ) files
