(** Checking the well-formedness of a program in [Ast] *)

open Ast
open Error
open Constant
open PrintCommon
open PPrint

(** Helpers ----------------------------------------------------------------- *)

let print_location lids =
  separate_map (string ", in ") print_lident lids

let ploc = printf_of_pprint print_location
let plid = printf_of_pprint print_lident
let ptyp = printf_of_pprint PrintAst.print_typ
let pdecl = printf_of_pprint_pretty PrintAst.print_decl
let pexpr = printf_of_pprint_pretty PrintAst.print_expr

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
      throw_error "[Checker.lookup_type] internal error %a not found" plid lid
  | x ->
      x

let possibly_warn =
  let h = Hashtbl.create 41 in
  fun lid ->
    match Hashtbl.find h lid with
    | exception Not_found ->
        Hashtbl.add h lid ();
        KPrint.beprintf "Notice: global name %a referenced but not defined, \
          please provide a C-level implementation!\n" plid lid
    | () ->
        ()

let lookup_global env lid =
  match M.find lid env.globals with
  | exception Not_found ->
      possibly_warn lid;
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


(** Checking ---------------------------------------------------------------- *)

let rec check_everything files =
  let env = populate_env files in
  List.iter (check_program env) files

and check_program env (_, decls) =
  List.iter (check_decl env) decls

and check_decl env d =
  let check env name t body =
    begin try
      let env = locate env name in
      check_expr env t body
    with Error msg ->
      KPrint.beprintf "%s\nDefinition:\n%a\n" msg pdecl d;
      Printexc.print_backtrace stderr;
      exit 253
    end
  in
  match d with
  | DFunction (t, name, binders, body) ->
      let env = List.fold_left push env binders in
      check env name t body
  | DGlobal (name, t, body) ->
      check env name t body
  | DTypeAlias _
  | DTypeFlat _ ->
      (* Barring any parameterized types, there's is nothing to check here
       * really. *)
      ()

and infer_expr env = function
  | EBound i ->
      begin try
        (find env i).typ
      with Not_found ->
        throw_error "In %a, bound variable %d is malformed" ploc env.location i
      end

  | EOpen (name, _) ->
      throw_error "In %a, there is an open variable %s" ploc env.location name

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
          throw_error "In %a, not a function being applied" ploc env.location;
        if List.length t_args <> List.length ts then
          throw_error "In %a, this is a partial application:\n%a" ploc env.location pexpr e;
        List.iter2 (check_types_equal env) ts t_args;
        t_ret

  | ELet (binder, body, cont) ->
      check_expr (locate env ([], binder.name)) binder.typ body;
      let env = push env binder in
      infer_expr env cont

  | EIfThenElse (e1, e2, e3, typ) ->
      check_expr env TBool e1;
      check_expr env typ e2;
      check_expr env typ e3;
      typ

  | ESequence es ->
      begin match List.rev es with
      | last :: rest ->
          List.iter (check_expr env TUnit) (List.rev rest);
          infer_expr env last
      | [] ->
        throw_error "In %a, there is an empty sequence" ploc env.location;
      end

  | EAssign (e1, e2) ->
      begin match e1 with
      | EBound i ->
          let binder = find env i in
          if not binder.mut then
            throw_error "In %a, this is not a mutable binding" ploc env.location;
          check_expr env binder.typ e2;
          binder.typ
      | _ ->
          throw_error "In %a, there is an assignment to a non-local" ploc env.location
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

  | EMatch (e, bs, t_ret) ->
      let t = infer_expr env e in
      check_branches env t_ret bs t;
      t_ret

  | EOp (op, w) ->
      begin match op with
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
          throw_error "In %a, this operator for internal use only" ploc env.location;
      end

  | EPushFrame | EPopFrame ->
      TUnit

  | EAny | EAbort | EReturn _ ->
      (** TODO: check that [EReturn] matches the expected return type *)
      TAny

  | EBool _ ->
      TBool

  | EFlat (lid, fieldexprs) ->
      let fieldtyps = assert_flat env (lookup_type env lid) in
      List.iter (fun (field, expr) ->
        check_expr env (List.assoc field fieldtyps) expr
      ) fieldexprs;
      TQualified lid

  | EField (lid, e, field) ->
      check_expr env (TQualified lid) e;
      List.assoc field (assert_flat env (lookup_type env lid))

  | EWhile (e1, e2) ->
      check_expr env TBool e1;
      check_expr env TUnit e2;
      TUnit

  | EBufCreateL es ->
      begin match es with
      | [] ->
          throw_error "In %a, there is an empty buf create sequence" ploc env.location
      | first :: others ->
          let t = infer_expr env first in
          List.iter (check_expr env t) others;
          TBuf t
      end

and check_branches env t_ret branches t_scrutinee =
  List.iter (fun (pat, expr) ->
    check_pat env t_scrutinee pat;
    let env = List.fold_left push env (binders_of_pat pat) in
    check_expr env t_ret expr
  ) branches

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
      throw_error "In %a, this is not a record definition" ploc env.location

and assert_buffer env e1 =
  match reduce env (infer_expr env e1) with
  | TBuf t1 ->
      t1
  | _ ->
      throw_error "In %a, this is not a buffer" ploc env.location

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
    throw_error "In %a, type mismatch, %a vs %a" ploc env.location ptyp t1 ptyp t2

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
