(** Going from CStar to CFlat *)

module CS = CStar
module CF = CFlat

module K = Constant

module StringMap = Map.Make(String)


(** Sizes *)

open CFlat.Sizes

(** We know how much space is needed to represent each C* type. *)
let size_of (t: CS.typ): size =
  match t with
  | CS.Int w ->
      size_of_width w
  | CS.Array _
  | CS.Pointer _ ->
      I32
  | CS.Void  ->
      invalid_arg ("size_of: only for expression types, got: " ^ CS.show_typ t)
  | CS.Qualified _ ->
      invalid_arg "Inlining.ml should get rid of top-level qualified names"
  | CS.Enum _
  | CS.Bool ->
      I32
  | CS.Z ->
      invalid_arg "Z is currently unused?!"
  | CS.Struct _
  | CS.Union _ ->
      failwith "not implemented"
  | CS.Function (_,_,_) ->
      failwith "not implemented"

let max s1 s2 =
  match s1, s2 with
  | I32, I32 -> I32
  | _ -> I64

let array_size_of (t: CS.typ): array_size =
  match t with
  | CS.Int w ->
      array_size_of_width w
  | CS.Array _
  | CS.Pointer _ ->
      A32
  | CS.Void  ->
      invalid_arg ("size_of: only for expression types, got: " ^ CS.show_typ t)
  | CS.Qualified _ ->
      invalid_arg "Inlining.ml should get rid of top-level qualified names"
  | CS.Enum _ ->
      A32
  | CS.Bool ->
      failwith "todo: packed arrays of bools"
  | CS.Z ->
      invalid_arg "Z is currently unused?!"
  | CS.Struct _
  | CS.Union _ ->
      failwith "not implemented"
  | CS.Function (_,_,_) ->
      failwith "not implemented"


(** Environments.
 *
 * Variable declarations are visited in infix order; this order is used for
 * numbering the corresponding Cflat local declarations. Wasm will later on take
 * care of register allocation. *)

(** We keep track, for each C* variable (a string), of its index in the stack
 * frame, along with its size. Enumeration constants are assigned a distinct
 * integer. *)
type env = {
  vars: (string * (CF.var * size)) list;
  enums: int StringMap.t;
}

let empty = {
  vars = [];
  enums = StringMap.empty;
}

(** Bind a new C* variable and get back the correponding var *)
let bind (env: env) (binder: CS.binder): env * CF.var =
  let i = List.length env.vars in {
    env with
    vars = (binder.CS.name, (i, size_of binder.CS.typ)) :: env.vars
  }, i

(** Same as [bind], but only returns the environment, suitable for using with
 * [fold_left]. *)
let extend env binder =
  fst (bind env binder)

(** Find a variable in the environment. *)
let find env v =
  List.assoc v env.vars


(** The actual translation. *)

let rec mk_expr (env: env) (e: CS.expr): CF.expr =
  match e with
  | CS.Var v ->
      let i, _ = find env v in
      CF.Var i

  | CS.Call (CS.Op (o, w), es) ->
      CF.CallOp ((w, o), List.map (mk_expr env) es)

  | CS.Call (CS.Qualified ident, es) ->
      CF.CallFunc (ident, List.map (mk_expr env) es)

  | CS.Constant (w, lit) ->
      CF.Constant (w, lit)

  | CS.InlineComment (_, e, _) ->
      mk_expr env e

  | CS.Qualified v ->
      (* JP: suboptimal, use an EEnum node instead in CStar? *)
      begin try
        CF.Constant (K.UInt32, string_of_int (StringMap.find v env.enums))
      with Not_found ->
        CF.Qualified v
      end

  | CS.BufCreate (l, e1, e2, t) ->
      CF.BufCreate (l, mk_expr env e1, mk_expr env e2, array_size_of t)

  | CS.BufCreateL (l, es, t) ->
      CF.BufCreateL (l, List.map (mk_expr env) es, array_size_of t)

  | CS.BufRead (e1, e2, t) ->
      CF.BufRead (mk_expr env e1, mk_expr env e2, array_size_of t)

  | CS.BufSub (e1, e2, t) ->
      CF.BufSub (mk_expr env e1, mk_expr env e2, array_size_of t)

  | CS.Bool b ->
      CF.Constant (K.Bool, if b then "1" else "0")

  | CS.Comma (e1, e2) ->
      CF.Comma (mk_expr env e1, mk_expr env e2)

  | CS.Cast (e, CS.Int wf, CS.Int wt) ->
      CF.Cast (mk_expr env e, wf, wt)

  | _ ->
      failwith ("not implemented (expr); got: " ^ CS.show_expr e)

let assert_var = function
  | CF.Var i -> i
  | _ -> invalid_arg "assert_var"

let rec mk_stmts (env: env) (stmts: CS.stmt list): env * CF.stmt list =
  match stmts with
  | [] ->
      env, []

  | CS.Decl (binder, e) :: stmts ->
      let e = mk_expr env e in
      let env, v = bind env binder in
      let env, stmts = mk_stmts env stmts in
      env, CF.Assign (v, e) :: stmts

  | CS.IfThenElse (e, stmts1, stmts2) :: stmts ->
      let e = mk_expr env e in
      let env, stmts1 = mk_stmts env stmts1 in
      let env, stmts2 = mk_stmts env stmts2 in
      let env, stmts = mk_stmts env stmts in
      env, CF.IfThenElse (e, stmts1, stmts2) :: stmts

  | CS.Return e :: stmts ->
      let env, stmts = mk_stmts env stmts in
      env, CF.Return (Option.map (mk_expr env) e) :: stmts

  | CS.Abort :: _ ->
      env, [ CF.Abort ]

  | CS.Ignore e :: stmts ->
      let env, stmts = mk_stmts env stmts in
      env, CF.Ignore (mk_expr env e) :: stmts

  | CS.While (e, block) :: stmts ->
      let env, block = mk_stmts env block in
      let env, stmts = mk_stmts env stmts in
      env, CF.While (mk_expr env e, block) :: stmts

  | CS.Assign (e, e') :: stmts ->
      let env, stmts = mk_stmts env stmts in
      let e = mk_expr env e in
      let e' = mk_expr env e' in
      env, CF.Assign (assert_var e, e') :: stmts

  | CS.Copy (dst, t, src) :: stmts ->
      let elt_size, elt_count =
        match t with
        | CS.Array (t, e) -> size_of t, mk_expr env e
        | _ -> failwith "Copy / Array?"
      in
      let dst = mk_expr env dst in
      let src = mk_expr env src in
      let env, stmts = mk_stmts env stmts in
      env, CF.Copy (dst, src, elt_size, elt_count) :: stmts

  | CS.Switch (e, branches) :: stmts ->
      let e = mk_expr env e in
      let env, branches = List.fold_left (fun (env, branches) branch ->
        let i, stmts = branch in
        let e = CF.Constant (K.UInt32, string_of_int (StringMap.find i env.enums)) in
        let env, stmts = mk_stmts env stmts in
        env, (e, stmts) :: branches
      ) (env, []) branches in
      let branches = List.rev branches in
      let env, stmts = mk_stmts env stmts in
      env, CF.Switch (e, branches) :: stmts

  | CS.BufWrite (e1, e2, e3, t) :: stmts ->
      let env, stmts = mk_stmts env stmts in
      let e1 = mk_expr env e1 in
      let e2 = mk_expr env e2 in
      let e3 = mk_expr env e3 in
      env, CF.BufWrite (e1, e2, e3, array_size_of t) :: stmts

  | CS.BufBlit (e1, e2, e3, e4, e5, t) :: stmts ->
      let env, stmts = mk_stmts env stmts in
      let e1 = mk_expr env e1 in
      let e2 = mk_expr env e2 in
      let e3 = mk_expr env e3 in
      let e4 = mk_expr env e4 in
      let e5 = mk_expr env e5 in
      env, CF.BufBlit (e1, e2, e3, e4, e5, array_size_of t) :: stmts

  | CS.BufFill (e1, e2, e3, t) :: stmts ->
      let env, stmts = mk_stmts env stmts in
      let e1 = mk_expr env e1 in
      let e2 = mk_expr env e2 in
      let e3 = mk_expr env e3 in
      env, CF.BufFill (e1, e2, e3, array_size_of t) :: stmts

  | CS.PushFrame :: stmts ->
      let env, stmts = mk_stmts env stmts in
      env, CF.PushFrame :: stmts

  | CS.PopFrame :: stmts ->
      let env, stmts = mk_stmts env stmts in
      env, CF.PopFrame :: stmts

  | CS.Comment _ :: stmts ->
      mk_stmts env stmts

let mk_decl env (d: CS.decl): CF.decl option =
  match d with
  | CS.Function (_, flags, ret, name, args, body) ->
      let public = not (List.exists ((=) Common.Private) flags) in
      let env = List.fold_left extend env args in
      let env, body = mk_stmts env body in
      let ret = match ret with
        | CS.Void -> []
        | _ -> [ size_of ret ]
      in
      let args, locals =
        KList.split_at (List.length args) (List.map (fun (_, (_, s)) -> s) env.vars)
      in
      Some CF.(Function { name; args; ret; locals; body; public })

  | CS.Type _ ->
      (* Not translating type declarations. *)
      None

  | CS.Global (name, flags, typ, body) ->
      let public = not (List.exists ((=) Common.Private) flags) in
      let size = size_of typ in
      let body = mk_expr env body in
      Some (CF.Global (name, size, body, public))

  | _ ->
      failwith ("not implemented (decl); got: " ^ CS.show_decl d)

let mk_module env (name, decls) =
  name, KList.filter_map (fun d ->
    try
      mk_decl env d
    with e ->
      (* Remove when everything starts working *)
      KPrint.beprintf "[C*ToC-] Couldn't translate %s:\n%s\n%s\n"
        (CS.ident_of_decl d) (Printexc.to_string e)
        (Printexc.get_backtrace ());
      None
  ) decls

let mk_files files =
  let env = List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | CS.Type (_, CS.Enum idents) ->
          KList.fold_lefti (fun i env ident ->
            { env with enums =
              StringMap.add ident i env.enums }
          ) env idents
      | _ ->
          env
    ) env decls
  ) empty files in
  List.map (mk_module env) files
