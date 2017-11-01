(** A bunch of little helpers to deal with our AST. *)

open Ast
open Warnings
open DeBruijn
open PrintAst.Ops

(* Some more fancy visitors ***************************************************)

let visit_files (env: 'env) (visitor: _ map) (files: file list) =
  KList.filter_map (fun f ->
    try
      Some (visitor#visit_file env f)
    with Error e ->
      maybe_fatal_error (fst f ^ "/" ^ fst e, snd e);
      None
  ) files


class ignore_everything = object
  method dfunction () cc flags n ret name binders expr =
    DFunction (cc, flags, n, ret, name, binders, expr)

  method dglobal () flags name typ expr =
    DGlobal (flags, name, typ, expr)

  method dtype () name flags n t fwd_decl =
    DType (name, flags, n, t, fwd_decl)
end

(** For each declaration in [files], call [f map decl], where [map] is the map
 * being filled. *)
let build_map files f =
  let map = Hashtbl.create 41 in
  iter_decls (f map) files;
  map


(* Creating AST nodes *********************************************************)

let uint32 = TInt K.UInt32

let type_of_op op w =
  let open Constant in
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
      invalid_arg "type_of_op"

let any = with_type TAny EAny
let eunit = with_type TUnit EUnit
let efalse = with_type TBool (EBool false)
let etrue = with_type TBool (EBool true)

let with_unit x = with_type TUnit x

let zerou32 = with_type uint32 (EConstant (K.UInt32, "0"))
let oneu32 = with_type uint32 (EConstant (K.UInt32, "1"))

let zerou8 =
  with_type (TInt (K.UInt8)) (EConstant (K.UInt8, "0"))

let pwild = with_type TAny PWild

let mk_op op w =
  { node = EOp (op, w);
    typ = type_of_op op w }

(* @0 < <finish> *)
let mk_lt finish =
  with_type TBool (
    EApp (mk_op K.Lt K.UInt32, [
      with_type uint32 (EBound 0);
      finish ]))

(* @0 <- @0 + 1ul *)
let mk_incr =
  with_type TUnit (
    EAssign (with_type uint32 (
      EBound 0), with_type uint32 (
      EApp (mk_op K.Add K.UInt32, [
        with_type uint32 (EBound 0);
        oneu32 ]))))

let mk_neq e1 e2 =
  with_type TBool (EApp (mk_op K.Neq K.UInt32, [ e1; e2 ]))

let mk_not e1 =
  with_type TBool (EApp (mk_op K.Not K.Bool, [ e1 ]))

let mk_and e1 e2 =
  with_type TBool (EApp (mk_op K.And K.Bool, [ e1; e2 ]))


let mk_uint32 i =
  with_type (TInt K.UInt32) (EConstant (K.UInt32, string_of_int i))

(* e - 1 *)
let mk_minus_one e =
  with_type uint32 (
    EApp (
      mk_op K.Sub K.UInt32, [
      e;
      oneu32
    ]))

(* e > 0 *)
let mk_gt_zero e =
  with_type TBool (
    EApp (mk_op K.Gt K.UInt32, [
      e;
      zerou32]))

(* *e *)
let mk_deref t e =
  with_type t (EBufRead (with_type (TBuf t) e, zerou32))

(* Binder nodes ***************************************************************)

let fresh_binder ?(mut=false) name typ =
  with_type typ { name; mut; mark = ref 0; meta = None; atom = Atom.fresh () }

let mark_mut b =
  { b with node = { b.node with mut = true }}

let sequence_binding () = with_type TUnit {
  name = "_";
  mut = false;
  mark = ref 0;
  meta = Some MetaSequence;
  atom = Atom.fresh ()
}

let unused_binding = sequence_binding

let mk_binding name t =
  let b = fresh_binder name t in
  b,
  { node = EOpen (b.node.name, b.node.atom); typ = t }

(** Generates "let [[name]]: [[t]] = [[e]] in [[name]]" *)
let mk_named_binding name t e =
  let b, ref = mk_binding name t in
  b,
  { node = e; typ = t },
  ref


(* Inspecting and destructuring nodes *****************************************)

let flatten_arrow =
  let rec flatten_arrow acc = function
    | TArrow (t1, t2) -> flatten_arrow (t1 :: acc) t2
    | t -> t, List.rev acc
  in
  flatten_arrow []

let fold_arrow ts t_ret =
  List.fold_right (fun t arr -> TArrow (t, arr)) ts t_ret

let is_array = function TArray _ -> true | _ -> false

(* If [e2] is assigned into an expression of type [t], we can sometimes
 * strengthen the type [t] into an array type. *)
let strengthen_array' t e2 =
  let ensure_buf = function TBuf t -> t | _ -> failwith "not a buffer" in
  let open Common in
  match t, e2.node with
  | TArray _, _ ->
      Some t

  | _, EBufCreateL (Stack, l) ->
      let t = ensure_buf t in
      Some (TArray (t, (K.Int32, string_of_int (List.length l))))

  | _, EBufCreate (Stack, _, size) ->
      let t = ensure_buf t in
      begin match size.node with
      | EConstant k ->
          Some (TArray (t, k))
      | _ ->
          None
      end

  | _ ->
      Some t

let strengthen_array t e2 =
  match strengthen_array' t e2 with
  | Some t ->
      t
  | None ->
      Warnings.fatal_error "In expression:\n%a\nthe array needs to be \
        hoisted (to the nearest enclosing push_frame, for soundness, or to \
        the nearest C block scope, for C89), but its \
        size is non-constant, so I don't know what declaration to write"
        pexpr e2


let is_X_value self (e: expr) =
  match e.node with
  | EBound _
  | EOpen _
  | EOp _
  | EQualified _
  | EConstant _
  | EUnit
  | EBool _
  | EEnum _
  | EString _
  | EFun _
  | EAbort _
  | EAddrOf _
  | EAny ->
      true

  | ETuple es
  | ECons (_, es) ->
      List.for_all self es

  | EFlat identexprs ->
      List.for_all (fun (_, e) -> self e) identexprs

  | EIgnore e
  | EField (e, _)
  | EComment (_, e, _)
  | ECast (e, _) ->
      self e

  | EApp _
  | ELet _
  | EIfThenElse _
  | ESequence _
  | EAssign _
  | EBufCreate _
  | EBufCreateL _
  | EBufRead _
  | EBufWrite _
  | EBufSub _
  | EBufBlit _
  | EBufFill _
  | EPushFrame
  | EPopFrame
  | EMatch _
  | ESwitch _
  | EReturn _
  | EBreak
  | EFor _
  | ETApp _
  | EWhile _ ->
      false

let rec is_value e =
  is_X_value is_value e

let rec is_pure_c_value e =
  is_X_value (fun e ->
    match e.node with
    | EBufRead (e1, e2)
    | EBufSub (e1, e2) ->
        is_pure_c_value e1 &&
        is_pure_c_value e2
    | _ ->
        is_X_value is_pure_c_value e
  ) e

let rec is_constant e =
  match e.node with
  | EConstant _ ->
      true
  | ECast (e, _) ->
      is_constant e
  | _ ->
      false

let assert_tlid t =
  (* We only have nominal typing for variants. *)
  match t with TQualified lid -> lid | _ -> assert false

let assert_tbuf t =
  match t with TBuf t -> t | _ -> assert false

let assert_elid t =
  (* We only have nominal typing for variants. *)
  match t with EQualified lid -> lid | _ -> assert false


(* Somewhat more advanced helpers *********************************************)

let rec strip_cast e =
  match e.node with
  | ECast (e, _) ->
      strip_cast e
  | _ ->
      e

let rec nest bs t e2 =
  match bs with
  | (b, e1) :: bs ->
      { node = ELet (b, e1, close_binder b (nest bs t e2)); typ = t }
  | [] ->
      e2

(** Substitute [es] in [e], possibly introducing intermediary let-bindings for
 * things that are not values. [t] is the type of [e]. *)
let safe_substitution es e t =
  (* We use a syntactic criterion to ensure that all the arguments are
   * values, i.e. can be safely substituted inside the function
   * definition. *)
  let bs, es = KList.fold_lefti (fun i (bs, es) e ->
    if not (is_value e) then
      let x, atom = mk_binding (Printf.sprintf "x%d" i) e.typ in
      (x, e) :: bs, atom :: es
    else
      bs, e :: es
  ) ([], []) es in
  let bs = List.rev bs in
  let es = List.rev es in
  nest bs t (DeBruijn.subst_n e es)

(* Descend into a terminal position, then call [f] on the sub-term in terminal
 * position. This function is only safe to call if all binders have been opened. *)
let rec nest_in_return_pos i typ f e =
  match e.node with
  | ELet (b, e1, e2) ->
      let e2 = nest_in_return_pos (i + 1) typ f e2 in
      { node = ELet (b, e1, e2); typ }
  | EIfThenElse (e1, e2, e3) ->
      let e2 = nest_in_return_pos i typ f e2 in
      let e3 = nest_in_return_pos i typ f e3 in
      { node = EIfThenElse (e1, e2, e3); typ }
  | ESwitch (e, branches) ->
      let branches = List.map (fun (t, e) ->
        t, nest_in_return_pos i typ f e
      ) branches in
      { node = ESwitch (e, branches); typ }
  | EMatch _ ->
      failwith "Matches should've been desugared"
  | _ ->
      f i e

let nest_in_return_pos = nest_in_return_pos 0

let push_ignore = nest_in_return_pos TUnit (fun _ e -> with_type TUnit (EIgnore (strip_cast e)))
