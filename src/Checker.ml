(** Checking the well-formedness of a program in [Ast] *)

open Ast
open Warnings
open Constant
open Location

let pop = PrintAst.pop
let plid = PrintAst.plid
let ptyp = PrintAst.ptyp
let pdecl = PrintAst.pdecl
let pexpr = PrintAst.pexpr

(** Environments ------------------------------------------------------------ *)

module M = Map.Make(struct
  type t = lident
  let compare = compare
end)

let uint32 = TInt UInt32

type env = {
  globals: typ M.t;
  locals: binder list;
  types: type_def M.t;
  location: loc list;
  enums: lident M.t;
}

let empty: env = {
  globals = M.empty;
  locals = [];
  types = M.empty;
  location = [];
  enums = M.empty;
}

let push env binder =
  { env with locals = binder :: env.locals }

let find env i =
  List.nth env.locals i

let lookup_type env lid =
  match M.find lid env.types with
  | exception Not_found ->
      fatal_error "[Checker.lookup_type] internal error %a not found" plid lid
  | x ->
      x

let possibly_warn =
  let h = Hashtbl.create 41 in
  fun env lid ->
    match Hashtbl.find h lid with
    | exception Not_found ->
        Hashtbl.add h lid ();
        maybe_fatal_error (KPrint.bsprintf "%a" ploc env.location,
          UnboundReference (KPrint.bsprintf "%a" plid lid))
    | () ->
        ()

let lookup_global env lid =
  match M.find lid env.globals with
  | exception Not_found ->
      possibly_warn env lid;
      TAny
  | x ->
      x

let populate_env files =
  List.fold_left (fun env (_, decls) ->
    List.fold_left (fun env decl ->
      match decl with
      | DType (lid, typ) ->
          let env = match typ with
          | Enum tags ->
              List.fold_left (fun env tag ->
                { env with enums = M.add tag lid env.enums }
              ) env tags
          | _ ->
              env
          in
          { env with types = M.add lid typ env.types }
      | DGlobal (_, lid, t, _) ->
          { env with globals = M.add lid t env.globals }
      | DFunction (_, _, ret, lid, binders, _) ->
          let t = List.fold_right (fun b t2 -> TArrow (b.typ, t2)) binders ret in
          { env with globals = M.add lid t env.globals }
      | DExternal (_, lid, typ) ->
          { env with globals = M.add lid typ env.globals }
    ) env decls
  ) empty files

let locate env loc =
  { env with location = update_location env.location loc }

(** Errors ------------------------------------------------------------------ *)

let type_error env fmt =
  Printf.kbprintf (fun buf ->
    raise_error_l (KPrint.bsprintf "%a" ploc env.location, TypeError (Buffer.contents buf))
  ) (Buffer.create 16) fmt

(** Checking ---------------------------------------------------------------- *)

let type_of_op env op w =
  match op with
  | Add | AddW | Sub | SubW | Div | DivW | Mult | MultW | Mod
  | BOr | BAnd | BXor ->
      TArrow (TInt w, TArrow (TInt w, TInt w))
  | BShiftL | BShiftR ->
      TArrow (TInt w, TArrow (uint32, TInt w))
  | Eq | Neq ->
      TArrow (TAny, TArrow (TAny, TBool))
  | Lt | Lte | Gt | Gte ->
      TArrow (TInt w, TArrow (TInt w, TBool))
  | And | Or | Xor ->
      TArrow (TBool, TArrow (TBool, TBool))
  | Not ->
      TArrow (TBool, TBool)
  | BNot ->
      TArrow (TInt w, TInt w)
  | Assign | PreIncr | PreDecr | PostIncr | PostDecr | Comma ->
      fatal_error "%a, operator %a is for internal use only" ploc env.location pop op


let rec check_everything files =
  let env = populate_env files in
  KList.filter_map (fun p ->
    try
      check_program env p;
      Some p
    with Error e ->
      Warnings.maybe_fatal_error e;
      KPrint.beprintf "Dropping %s (at checking time)\n" (fst p);
      None
  ) files

and check_program env (name, decls) =
  let env = locate env (In name) in
  List.iter (check_decl env) decls

and check_decl env d =
  match d with
  | DFunction (_, _, t, name, binders, body) ->
      let env = List.fold_left push env binders in
      let env = locate env (InTop name) in
      check_expr env t body
  | DGlobal (_, name, t, body) ->
      let env = locate env (InTop name) in
      check_expr env t body
  | DExternal _
  | DType _ ->
      (* Barring any parameterized types, there's is nothing to check here
       * really. *)
      ()

and infer_expr env e =
  let t = infer_expr' env e.node e.typ in
  check_subtype env t e.typ;
  e.typ <- t;
  t

and infer_expr' env e t =
  match e with
  | EBound i ->
      begin try
        (find env i).typ
      with Not_found ->
        type_error env "bound variable %d is malformed" i
      end

  | EOpen (name, _) ->
      type_error env "there is an open variable %s" name

  | EQualified lid ->
      lookup_global env lid

  | EConstant (w, _) ->
      TInt w

  | EUnit ->
      TUnit

  | ECast (e, t) ->
      check_expr env TAny e;
      t

  | EApp (e, es) ->
      let t = infer_expr env e in
      if t = TAny then
        let _ = List.map (infer_expr env) es in
        TAny
      else
        let ts = List.map (infer_expr env) es in
        let t_ret, t_args = flatten_arrow t in
        if List.length t_args = 0 then
          type_error env "Not a function being applied:\n%a" pexpr e;
        if List.length t_args <> List.length ts then
          type_error env "This is a partial application:\n%a" pexpr e;
        List.iter2 (check_subtype env) ts t_args;
        t_ret

  | ELet (binder, body, cont) ->
      check_expr (locate env (In binder.node.name)) binder.typ body;
      let env = push env binder in
      infer_expr (locate env (After binder.node.name)) cont

  | EIfThenElse (e1, e2, e3) ->
      check_expr env TBool e1;
      let t1 = infer_expr (locate env Then) e2 in
      let t2 = infer_expr (locate env Else) e3 in
      check_eqtype env t1 t2;
      t1

  | ESequence es ->
      begin match List.rev es with
      | last :: rest ->
          List.iter (check_expr env TUnit) (List.rev rest);
          infer_expr env last
      | [] ->
          type_error env "Empty sequence"
      end

  | EAssign (e1, e2) ->
      let t = check_valid_assignment_lhs env e1 in
      check_expr env t e2;
      TUnit

  | EBufCreate (e1, e2) ->
      let t1 = infer_expr env e1 in
      check_expr env uint32 e2;
      TBuf t1

  | EBufRead (e1, e2) ->
      check_expr env uint32 e2;
      assert_buffer env e1

  | EBufWrite (e1, e2, e3) ->
      check_expr env uint32 e2;
      let t1 = assert_buffer env e1 in
      check_expr env t1 e3;
      TUnit

  | EBufSub (e1, e2) ->
      check_expr env uint32 e2;
      let t1 = assert_buffer env e1 in
      TBuf t1

  | EBufBlit (b1, i1, b2, i2, len) ->
      let t1 = assert_buffer env b1 in
      check_expr env (TBuf t1) b2;
      check_expr env uint32 i1;
      check_expr env uint32 i2;
      check_expr env uint32 len;
      TUnit

  | EOp (op, w) ->
      type_of_op env op w

  | EPushFrame | EPopFrame ->
      TUnit

  | EAny | EAbort ->
      TAny

  | EReturn e ->
      ignore (infer_expr env e);
      (** TODO: check that [EReturn] matches the expected return type *)
      TAny

  | EBool _ ->
      TBool

  | EWhile (e1, e2) ->
      check_expr env TBool e1;
      check_expr env TUnit e2;
      TUnit

  | EBufCreateL es ->
      begin match es with
      | [] ->
          fatal_error "%a, there is an empty buf create sequence" ploc env.location
      | first :: others ->
          let t = infer_expr env first in
          List.iter (check_expr env t) others;
          TBuf t
      end

  | ETuple es ->
      TTuple (List.map (infer_expr env) es)

  | ECons (ident, exprs) ->
      (** The typing rules of matches and constructors are always nominal;
       * structural types appear through simplification phases, which also
       * remove matches in favor of switches or conditionals. *)
      let lid = assert_qualified env t in
      let ts = List.map (infer_expr env) exprs in
      let ts' = fst (List.split (snd (List.split (assert_cons_of env (lookup_type env lid) ident)))) in
      List.iter2 (check_subtype env) ts ts';
      TQualified lid

  | EMatch (e, bs) ->
      let t_scrutinee = infer_expr env e in
      check_branches env t t_scrutinee bs

  | EFlat fieldexprs ->
      (** Just like a constructor and a match, a record and field expressions
       * construct and destruct values of matching kinds, except that structural
       * typing comes into play. Indeed, a flat record is typed nominally (if
       * the context demands it) or structurally (default). TODO just type
       * structurally, and let the subtyping relation do the rest? *)
      begin try
        let lid = assert_qualified env t in
        let fieldtyps = assert_flat env (lookup_type env lid) in
        if List.length fieldexprs <> List.length fieldtyps then
          type_error env "some fields are either missing or superfluous";
        List.iter (fun (field, expr) ->
          let t, _ = List.assoc field fieldtyps in
          check_expr env t expr
        ) fieldexprs;
        TQualified lid
      with Not_found ->
        TAnonymous (Flat (List.map (fun (f, e) ->
          f, (infer_expr env e, false)
        ) fieldexprs))
      end

  | EField (e, field) ->
      (** Structs and unions have fields; they may be typed structurally or
       * nominally, and we shall dereference a field in both cases. *)
      let t = infer_expr env e in
      begin match t with
      | TQualified lid ->
          fst (find_field env lid field)
      | TAnonymous def ->
          fst (find_field_from_def env def field)
      | _ ->
          type_error env "this type doesn't have fields"
      end

  | EEnum tag ->
      (** Enums / Switches behave just like Flats / Fields; the constructor
       * gives rise to a structural or nominal type and the destructor works
       * with either a nominal or a structural type. *)
      begin try
        TQualified (M.find tag env.enums)
      with Not_found ->
        TAnonymous (Enum [ tag ])
      end

  | ESwitch (e, branches) ->
      begin match infer_expr env e with
      | TQualified lid ->
          check_eqntype env t (fun (tag, e) ->
            if not (M.find tag env.enums = lid) then
              type_error env "scrutinee has type %a but tag %a does not belong to \
                this type" plid lid plid tag;
            infer_expr env e
          ) branches

      | TAnonymous (Enum tags) as t ->
          check_eqntype env t (fun (tag, e) ->
            if not (List.exists ((=) tag) tags) then
              type_error env "scrutinee has type %a but tag %a does not belong to \
                this type" ptyp t plid tag;
            infer_expr env e
          ) branches

      | t ->
          type_error env "cannot switch on element of type %a" ptyp t
      end

and check_eqntype: 'a. env -> typ -> ('a -> typ) -> 'a list -> typ =
  fun env t_context f l ->
  let t_base = if t_context <> TAny then ref (Some t_context) else ref None in
  List.iter (fun elt ->
    let t = f elt in
    match !t_base with
    | Some t_base -> check_eqtype env t_base t
    | None -> t_base := Some t
  ) l;
  Option.must !t_base

and find_field env lid field =
  find_field_from_def env (lookup_type env lid) field

and find_field_from_def env def field =
  try begin match def with
    | Flat fields ->
        List.assoc field fields
    | Union fields ->
        begin match KList.find_opt (function
          | Some field', t when field = field' ->
              Some (t, false) (* not mutable *)
          | _ ->
              None
        ) fields with
        | Some t -> t
        | None -> raise Not_found
        end
    | _ ->
        raise Not_found
  end with Not_found ->
    type_error env "record or union type doesn't have a field named %s" field


(* Per Perry's definition, a path is a block id along with an offset, and a
 * possibly empty sequence of field names. We don't check (TODO) that after
 * rewritings, all paths are of that form. *)

(** This function checks that the left-hand side of assignments satisfies a
 * relaxed notion of path (to be formalized), which is either a locally mutable
 * variable (an extension on Perry's formalism) or an array access followed by a
 * non-empty series of field names, the last of which is mutable. *)
and check_valid_assignment_lhs env e =
  match e.node with
  | EBound i ->
      let binder = find env i in
      if not binder.node.mut then
        type_error env "%a (a.k.a. %s) is not a mutable binding" pexpr e binder.node.name;
      binder.typ
  | EField (e, f) ->
      let t1 = check_valid_path env e in
      let t2, mut = find_field env (assert_qualified env t1) f in
      if not mut then
        type_error env "the field %s of type %a is not marked as mutable" f ptyp t1;
      t2
  | _ ->
      type_error env "EAssign wants a lhs that's a mutable, local variable, or a \
        path to a mutable field"

and check_valid_path env e =
  match e.node with
  | EField (e, f) ->
      let t1 = check_valid_path env e in
      fst (find_field env (assert_qualified env t1) f)

  | EBufRead _
  | EBound _ ->
      infer_expr env e

  | _ ->
      type_error env "EAssign wants a lhs that's a mutable, local variable, or a \
        path to a mutable field"

and check_branches env t_context t_scrutinee branches =
  check_eqntype env t_context (fun (pat, expr) ->
    check_pat env t_scrutinee pat;
    let env = List.fold_left push env (binders_of_pat pat) in
    infer_expr env expr
  ) branches

and check_pat env t_context pat =
  match pat.node with
  | PVar b ->
      check_subtype env t_context b.typ;
      b.typ <- t_context;
      check_subtype env t_context pat.typ;
      pat.typ <- t_context
  | PUnit ->
      check_subtype env t_context TUnit;
      pat.typ <- t_context

  | PBool _ ->
      check_subtype env t_context TBool;
      pat.typ <- t_context

  | PTuple ps ->
      let ts = assert_tuple env t_context in
      List.iter2 (check_pat env) ts ps;
      pat.typ <- t_context

  | PCons (ident, pats) ->
      let lid = assert_qualified env t_context in
      let ts = fst (List.split (snd (List.split (assert_cons_of env (lookup_type env lid) ident)))) in
      List.iter2 (check_pat env) ts pats;
      pat.typ <- t_context

  | PRecord fieldpats ->
      let lid = assert_qualified env t_context in
      let fieldtyps = assert_flat env (lookup_type env lid) in
      List.iter (fun (field, pat) ->
        let t, _ =
          try
            List.assoc field fieldtyps
          with Not_found ->
            fatal_error "%a, type %a has no field named %s" ploc env.location plid lid field
        in
        check_pat env t pat
      ) fieldpats;
      pat.typ <- t_context

  | PEnum tag ->
      let lid = assert_qualified env t_context in
      assert (lid = M.find tag env.enums);
      pat.typ <- t_context


and assert_tuple env t =
  match t with
  | TTuple ts ->
      ts
  | _ ->
      fatal_error "%a, this is not a tuple type" ploc env.location

and assert_flat env t =
  match t with
  | Flat def ->
      def
  | _ ->
      fatal_error "%a, this is not a record definition" ploc env.location

and assert_qualified env t =
  match t with
  | TQualified lid ->
      lid
  | _ ->
      fatal_error "%a, expected a provided type annotation" ploc env.location

and assert_buffer env e1 =
  match expand_abbrev env (infer_expr env e1) with
  | TBuf t1 ->
      t1
  | TAny ->
      TAny
  | t ->
      match e1.node with
      | EBound i ->
          let b = find env i in
          type_error env "%a (a.k.a. %s) is not a buffer but a %a" pexpr e1 b.node.name ptyp b.typ
      | _ ->
          type_error env "%a is not a buffer but a %a" pexpr e1 ptyp t

and assert_cons_of env t id: fields_t =
  match t with
  | Variant branches ->
      begin try
        List.assoc id branches
      with Not_found ->
        fatal_error "%a, %s is not a constructor of the annotated type" ploc env.location id
      end
  | _ ->
      fatal_error "%a the annotated type is not a variant type" ploc env.location

and check_expr env t e =
  let t' = infer_expr env e in
  check_subtype env t' t

and subtype env t1 t2 =
  match expand_abbrev env t1, expand_abbrev env t2 with
  | TInt w1, TInt w2 when w1 = w2 ->
      true
  | TBuf t1, TBuf t2 when subtype env t1 t2 ->
      true
  | TUnit, TUnit ->
      true
  | TQualified _, TQualified _ ->
      (** Note: TQualified types are references to externally-defined types, for
       * which we know nothing about, so it may be the case that two seemingly
       * incompatible types (e.g. Prims.nat vs Prims.int) are actually
       * subtypes... *)
      true
  | TBool, TBool
  | _, TAny
  | TAny, _ ->
      true
  | TArrow (t1, t2), TArrow (t'1, t'2) when
    subtype env t1 t'1 &&
    subtype env t2 t'2 ->
      true
  | TZ, TZ ->
      true
  | TBound i, TBound i' ->
      i = i'
  | TApp (lid, args), TApp (lid', args') ->
      lid = lid' && List.for_all2 (eqtype env) args args'
  | TTuple ts1, TTuple ts2 ->
      List.length ts1 = List.length ts2 &&
      List.for_all2 (subtype env) ts1 ts2
  | _ ->
      false

and eqtype env t1 t2 =
  subtype env t1 t2 && subtype env t2 t1

and check_eqtype env t1 t2 =
  if not (eqtype env t1 t2) then
    type_error env "eqtype mismatch, %a (a.k.a. %a) vs %a (a.k.a. %a)"
      ptyp t1 ptyp (expand_abbrev env t1) ptyp t2 ptyp (expand_abbrev env t2)

and check_subtype env t1 t2 =
  if not (subtype env t1 t2) then
    type_error env "subtype mismatch, %a (a.k.a. %a) vs %a (a.k.a. %a)"
      ptyp t1 ptyp (expand_abbrev env t1) ptyp t2 ptyp (expand_abbrev env t2)

and expand_abbrev env t =
  match t with
  | TQualified lid ->
      begin match M.find lid env.types with
      | exception Not_found -> t
      | Abbrev (_, t) -> expand_abbrev env t
      | _ -> t
      end
  | TApp (lid, args) ->
      begin match M.find lid env.types with
      | exception Not_found -> t
      | Abbrev (_, t) -> expand_abbrev env (DeBruijn.subst_tn t args)
      | _ -> t
      end
  | _ ->
      t

let type_of_op = type_of_op empty
