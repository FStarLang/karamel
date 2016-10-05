(** Checking the well-formedness of a program in [Ast] *)

open Ast
open Warnings
open Constant
open PrintCommon
open PPrint

(** Helpers ----------------------------------------------------------------- *)

type loc =
  | In of string
  | InTop of lident
  | Then
  | Else
  | After of string

let print_loc = function
  | InTop l ->
      string "in declaration " ^^ print_lident l
  | In l ->
      string "in the definition of " ^^ string l
  | Then ->
      string "in the then branch"
  | Else ->
      string "in the else branch"
  | After s ->
      string "after the definition of " ^^ string s

let print_location locs =
  separate_map (string ", ") print_loc locs

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
  | Flat of (ident * (typ * bool)) list

let uint32 = TInt UInt32

type env = {
  globals: typ M.t;
  locals: binder list;
  types: tdecl M.t;
  location: loc list;
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
      | DTypeAlias (lid, _, typ) ->
          { env with types = M.add lid (Abbrev typ) env.types }
      | DTypeFlat (lid, fields) ->
          { env with types = M.add lid (Flat fields) env.types }
      | DGlobal (_, lid, t, _) ->
          { env with globals = M.add lid t env.globals }
      | DFunction (_, ret, lid, binders, _) ->
          let t = List.fold_right (fun b t2 -> TArrow (b.typ, t2)) binders ret in
          { env with globals = M.add lid t env.globals }
      | DExternal (lid, typ) ->
          { env with globals = M.add lid typ env.globals }
    ) env decls
  ) empty files

let locate env loc =
  { env with location =
    match loc, env.location with
    | After _, After _ :: locs ->
        loc :: locs
    | _ ->
        loc :: env.location }

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
  | DFunction (_, t, name, binders, body) ->
      let env = List.fold_left push env binders in
      let env = locate env (InTop name) in
      check_expr env t body
  | DGlobal (_, name, t, body) ->
      let env = locate env (InTop name) in
      check_expr env t body
  | DTypeAlias _
  | DExternal _
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
      check_expr (locate env (In binder.name)) binder.typ body;
      let env = push env binder in
      infer_expr (locate env (After binder.name)) cont

  | EIfThenElse (e1, e2, e3) ->
      check_expr env TBool e1;
      let t1 = infer_expr (locate env Then) e2 in
      let t2 = infer_expr (locate env Else) e3 in
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

  | EMatch (e, bs) ->
      let t_scrutinee = infer_expr env e in
      let t_ret = check_branches env t_scrutinee bs in
      t_ret

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

  | EFlat fieldexprs ->
      let lid = assert_qualified env t in
      let fieldtyps = assert_flat env (lookup_type env lid) in
      if List.length fieldexprs <> List.length fieldtyps then
        type_error env "some fields are either missing or superfluous";
      List.iter (fun (field, expr) ->
        let t, _ = List.assoc field fieldtyps in
        check_expr env t expr
      ) fieldexprs;
      TQualified lid

  | EField (e, field) ->
      let lid = assert_qualified env e.mtyp in
      check_expr env (TQualified lid) e;
      fst (find_field env lid field)


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

and find_field env lid field =
  begin try
    List.assoc field (assert_flat env (lookup_type env lid))
  with Not_found ->
    type_error env "%a, the type %a doesn't have a field named %s"
      ploc env.location plid lid field
  end


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
      if not binder.mut then
        type_error env "%a (a.k.a. %s) is not a mutable binding" pexpr e binder.name;
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
      fatal_error "%a, this is not a record definition" ploc env.location

and assert_qualified env t =
  match t with
  | TQualified lid ->
      lid
  | _ ->
      fatal_error "%a, expected a provided type annotation" ploc env.location

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
  | TBound i, TBound i' ->
      i = i'
  | TApp (lid, args), TApp (lid', args') ->
      lid = lid' && List.for_all2 (types_equal env) args args'
  | _ ->
      false

and check_types_equal env t1 t2 =
  if not (types_equal env t1 t2) then
    type_error env "type mismatch, %a (a.k.a. %a) vs %a (a.k.a. %a)"
      ptyp t1 ptyp (reduce env t1) ptyp t2 ptyp (reduce env t2)

and reduce env t =
  match t with
  | TQualified lid ->
      begin match M.find lid env.types with
      | exception Not_found -> t
      | Abbrev t -> reduce env t
      | _ -> t
      end
  | TApp (lid, args) ->
      begin match M.find lid env.types with
      | exception Not_found -> t
      | Abbrev t -> reduce env (DeBruijn.subst_tn t args)
      | _ -> t
      end
  | _ ->
      t

let type_of_op = type_of_op empty
