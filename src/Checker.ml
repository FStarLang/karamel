(** Checking the well-formedness of a program in [Ast] *)

open Ast
open Warnings
open Constant
open PrintCommon
open PPrint

(** Helpers ----------------------------------------------------------------- *)

let print_location lids =
  separate_map (string ", in ") print_lident lids

let ploc = printf_of_pprint print_location
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

type tdecl =
  | Abbrev of typ
  | Flat of (ident * typ) list

let uint32 = TInt UInt32

type env = {
  globals: typ M.t;
  locals: binder list;
  types: tdecl M.t;
  location: lident list;
}

let empty: env = {
  globals = M.empty;
  locals = [];
  types = M.empty;
  location = []
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
      | DTypeAlias (lid, typ) ->
          { env with types = M.add lid (Abbrev typ) env.types }
      | DTypeFlat (lid, fields) ->
          { env with types = M.add lid (Flat fields) env.types }
      | _ ->
          env
    ) env decls
  ) empty files

let locate env lid =
  { env with location = lid :: env.location }


(** Errors ------------------------------------------------------------------ *)

let type_error env fmt =
  Printf.kbprintf (fun buf ->
    raise_error_l (KPrint.bsprintf "%a" ploc env.location, TypeError (Buffer.contents buf))
  ) (Buffer.create 16) fmt

(** Checking ---------------------------------------------------------------- *)

let type_of_op env op w =
  match op with
  | Add | AddW | Sub | SubW | Div | Mult | Mod
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
  | Assign | PreIncr | PreDecr | PostIncr | PostDecr ->
      fatal_error "In %a, operator %a is for internal use only" ploc env.location pop op


let rec check_everything files =
  let env = populate_env files in
  KList.filter_map (fun p ->
    try
      check_program env p;
      Some p
    with Error e ->
      Warnings.maybe_fatal_error e;
      None
  ) files

and check_program env (name, decls) =
  let env = locate env ([], name) in
  List.iter (check_decl env) decls

and check_decl env d =
  match d with
  | DFunction (t, name, binders, body) ->
      let env = List.fold_left push env binders in
      let env = locate env name in
      check_expr env t body
  | DGlobal (name, t, body) ->
      let env = locate env name in
      check_expr env t body
  | DTypeAlias _
  | DTypeFlat _ ->
      (* Barring any parameterized types, there's is nothing to check here
       * really. *)
      ()

and infer_expr env e =
  let t = infer_expr' env e.node e.mtyp in
  if e.mtyp <> TAny then begin
    (* KPrint.bprintf "Checking %a (previously: %a)\n" pexpr e ptyp e.mtyp; *)
    check_types_equal env t e.mtyp;
  end;
  e.mtyp <- t;
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
        TAny
      else
        let ts = List.map (infer_expr env) es in
        let t_ret, t_args = flatten_arrow t in
        if List.length t_args = 0 then
          type_error env "Not a function being applied:\n%a" pexpr e;
        if List.length t_args <> List.length ts then
          type_error env "This is a partial application:\n%a" pexpr e;
        List.iter2 (check_types_equal env) ts t_args;
        t_ret

  | ELet (binder, body, cont) ->
      check_expr (locate env ([], binder.name)) binder.typ body;
      let env = push env binder in
      infer_expr env cont

  | EIfThenElse (e1, e2, e3) ->
      check_expr env TBool e1;
      let t1 = infer_expr (locate env ([], "if-then")) e2 in
      let t2 = infer_expr (locate env ([], "if-else")) e3 in
      check_types_equal env t1 t2;
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
      begin match e1.node with
      | EBound i ->
          let binder = find env i in
          if not binder.mut then
            type_error env "%a (a.k.a. %s) is not a mutable binding" pexpr e1 binder.name;
          check_expr env binder.typ e2;
          TUnit
      | _ ->
          type_error env "the lhs of an assignment should be an EBound"
      end

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

  | EMatch (e, bs) ->
      let t_scrutinee = infer_expr env e in
      let t_ret = check_branches env t_scrutinee bs in
      t_ret

  | EOp (op, w) ->
      type_of_op env op w

  | EPushFrame | EPopFrame ->
      TUnit

  | EAny | EAbort | EReturn _ ->
      (** TODO: check that [EReturn] matches the expected return type *)
      TAny

  | EBool _ ->
      TBool

  | EFlat fieldexprs ->
      let lid = assert_qualified env t in
      let fieldtyps = assert_flat env (lookup_type env lid) in
      List.iter (fun (field, expr) ->
        check_expr env (List.assoc field fieldtyps) expr
      ) fieldexprs;
      TQualified lid

  | EField (e, field) ->
      let lid = assert_qualified env e.mtyp in
      check_expr env (TQualified lid) e;
      List.assoc field (assert_flat env (lookup_type env lid))

  | EWhile (e1, e2) ->
      check_expr env TBool e1;
      check_expr env TUnit e2;
      TUnit

  | EBufCreateL es ->
      begin match es with
      | [] ->
          fatal_error "In %a, there is an empty buf create sequence" ploc env.location
      | first :: others ->
          let t = infer_expr env first in
          List.iter (check_expr env t) others;
          TBuf t
      end

and check_branches env t_scrutinee branches =
  assert (List.length branches > 0);
  let t_ret = ref None in
  List.iter (fun (pat, expr) ->
    check_pat env t_scrutinee pat;
    let env = List.fold_left push env (binders_of_pat pat) in
    match !t_ret with
    | None ->
        let t = infer_expr env expr in
        t_ret := Some t
    | Some t' ->
        let t = infer_expr env expr in
        check_types_equal env t t'
  ) branches;
  Option.must !t_ret

and check_pat env t = function
  | PVar b ->
      check_types_equal env t b.typ
  | PUnit ->
      check_types_equal env t TUnit
  | PBool _ ->
      check_types_equal env t TBool

and assert_flat env t =
  match t with
  | Flat def ->
      def
  | _ ->
      fatal_error "In %a, this is not a record definition" ploc env.location

and assert_qualified env t =
  match t with
  | TQualified lid ->
      lid
  | _ ->
      fatal_error "In %a, expected a provided type annotation" ploc env.location

and assert_buffer env e1 =
  match reduce env (infer_expr env e1) with
  | TBuf t1 ->
      t1
  | TAny ->
      TAny
  | t ->
      match e1.node with
      | EBound i ->
          let b = find env i in
          type_error env "%a (a.k.a. %s) is not a buffer but a %a" pexpr e1 b.name ptyp b.typ
      | _ ->
          type_error env "%a is not a buffer but a %a" pexpr e1 ptyp t

and check_expr env t e =
  let t' = infer_expr env e in
  check_types_equal env t t'

and types_equal env t1 t2 =
  match reduce env t1, reduce env t2 with
  | TInt w1, TInt w2 when w1 = w2 ->
      true
  | TBuf t1, TBuf t2 when types_equal env t1 t2 ->
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
    types_equal env t1 t'1 &&
    types_equal env t2 t'2 ->
      true
  | TZ, TZ ->
      true
  | _ ->
      false

and check_types_equal env t1 t2 =
  if not (types_equal env t1 t2) then
    raise_error (TypeError (KPrint.bsprintf "In %a, type mismatch, %a (a.k.a. %a) vs %a (a.k.a. %a)"
      ploc env.location ptyp t1 ptyp (reduce env t1) ptyp t2 ptyp (reduce env t2)))

and reduce env t =
  match t with
  | TQualified lid ->
      begin match M.find lid env.types with
      | exception Not_found -> t
      | Abbrev t -> reduce env t
      | _ -> t
      end
  | _ ->
      t

let type_of_op = type_of_op empty
