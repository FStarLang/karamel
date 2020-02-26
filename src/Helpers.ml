(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** A bunch of little helpers to deal with our AST. *)

open Ast
open DeBruijn
open PrintAst.Ops

(** For each declaration in [files], call [f map decl], where [map] is the map
 * being filled. *)
let build_map files f =
  let map = Hashtbl.create 41 in
  (object inherit [_] iter method visit_decl _ = f map end)#visit_files () files;
  map

module MkIMap (M: Map.S) = struct
  type key = M.key
  type 'data t = 'data M.t ref
  let create () = ref M.empty
  let clear m = m := M.empty
  let add k v m = m := M.add k v !m
  let find k m = M.find k !m
  let iter f m = M.iter f !m
end


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

let zero w = with_type (TInt w) (EConstant (w, "0"))
let zerou8 = zero K.UInt8
let zerou32 = zero K.UInt32
let one w = with_type (TInt w) (EConstant (w, "1"))
let oneu32 = one K.UInt32

let pwild = with_type TAny PWild

let mk_op op w =
  { node = EOp (op, w);
    typ = type_of_op op w }

(* @0 < <finish> *)
let mk_lt w finish =
  with_type TBool (
    EApp (mk_op K.Lt w, [
      with_type (TInt w) (EBound 0);
      finish ]))

let mk_lt32 =
  mk_lt K.UInt32

(* @0 <- @0 + 1ul *)
let mk_incr w =
  let t = TInt w in
  with_type TUnit (
    EAssign (with_type t (
      EBound 0), with_type t (
      EApp (mk_op K.Add w, [
        with_type t (EBound 0);
        one w ]))))

let mk_incr32 = mk_incr K.UInt32

let mk_neq e1 e2 =
  with_type TBool (EApp (mk_op K.Neq K.UInt32, [ e1; e2 ]))

let mk_not e1 =
  with_type TBool (EApp (mk_op K.Not K.Bool, [ e1 ]))

let mk_and e1 e2 =
  with_type TBool (EApp (mk_op K.And K.Bool, [ e1; e2 ]))

let mk_or e1 e2 =
  with_type TBool (EApp (mk_op K.Or K.Bool, [ e1; e2 ]))

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
let mk_deref t ?(const=false) e =
  with_type t (EBufRead (with_type (TBuf (t, const)) e, zerou32))

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

let mk_binding ?(mut=false) name t =
  let b = fresh_binder name t in
  { b with node = { b.node with mut } },
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

let is_union = function TAnonymous (Union _) -> true | _ -> false

let is_null = function
  | { node = EApp (
      { node = EQualified (
          ([ "LowStar"; "Buffer" ] | [ "C"; "Nullity" ]), "null" |
          ([ "LowStar"; "Monotonic"; "Buffer" ], "mnull"));
        _ }, _); _ }
  ->
      true
  | _ ->
      false

let is_uu name = KString.starts_with name "uu__"

let pattern_matches p lid =
  Bundle.pattern_matches p (String.concat "_" (fst lid))

let is_static_header lid =
  List.exists (fun p -> pattern_matches p lid) !Options.static_header

(* If [e2] is assigned into an expression of type [t], we can sometimes
 * strengthen the type [t] into an array type. This is the only place that
 * generates TArray meaning every TArray implies Stack. *)
let strengthen_array' t e2 =
  let ensure_buf = function TBuf (t, _) -> t | _ -> failwith "not a buffer" in
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
      Warn.fatal_error "In expression:\n%a\nthe array needs to be \
        hoisted (to the nearest enclosing push_frame, for soundness, or to \
        the nearest C block scope, for C89), but its \
        size is non-constant, so I don't know what declaration to write"
        pexpr e2

let is_readonly_builtin_lid lid =
  let pure_builtin_lids = [
    [ "C"; "String" ], "get";
    [ "C"; "Nullity" ], "op_Bang_Star";
    [ "Lib"; "IntVector"; "Intrinsics" ], "vec128_smul64";
    [ "Lib"; "IntVector"; "Intrinsics" ], "vec256_smul64";
    ["LowStar"; "Monotonic"; "Buffer"], "mnull";
  ] in
  List.exists (fun lid' ->
    let lid = Idents.string_of_lident lid in
    let lid' = Idents.string_of_lident lid' in
    KString.starts_with lid lid'
  ) pure_builtin_lids

class ['self] readonly_visitor = object (self: 'self)
  inherit [_] reduce
  method private zero = true
  method private plus = (&&)
  method! visit_EStandaloneComment _ _ = false
  method! visit_EIfThenElse _ _ _ _ = false
  method! visit_ESequence _ _ = false
  method! visit_EAssign _ _ _ = false
  method! visit_EBufCreate _ _ _ _ = false
  method! visit_EBufCreateL _ _ _ = false
  method! visit_EBufWrite _ _ _ _ = false
  method! visit_EBufBlit _ _ _ _ _ _ = false
  method! visit_EBufFill _ _ _ _ = false
  method! visit_EBufFree _ _ = false
  method! visit_EMatch _ _ _ = false
  method! visit_ESwitch _ _ _ = false
  method! visit_EReturn _ _ = false
  method! visit_EBreak _ = false
  method! visit_EFor _ _ _ _ _ _ = false
  method! visit_ETApp _ _ _ = false
  method! visit_EWhile _ _ _ = false
  method! visit_EPushFrame _ = false
  (* PushFrame markers have a semantic meaning (they indicate the beginning of
   * scope for hoisting phases) so we cannot remove them. We, however, don't do
   * anything meaningful with PopFrames so they can be safely eliminated. *)

  method! visit_EApp _ e es =
    match e.node with
    | EOp _ ->
        List.for_all (self#visit_expr_w ()) es
    | EQualified lid when is_readonly_builtin_lid lid ->
        List.for_all (self#visit_expr_w ()) es
    | _ ->
        false
end

let is_readonly_c_expression = (new readonly_visitor)#visit_expr_w ()

class ['self] value_visitor = object (_self: 'self)
  inherit [_] readonly_visitor
  method! visit_EApp _ _ _ = false
  method! visit_ELet _ _ _ _ = false
  method! visit_EBufRead _ _ _ = false
  method! visit_EBufSub _ _ _ = false
  method! visit_EStandaloneComment _ _ = false
end

let is_value = (new value_visitor)#visit_expr_w ()

(* Used by the Checker for the size of stack-allocated buffers. Also used by the
 * global initializers collection phase. This is a conservative approximation of
 * the C11 standard 6.6 §6 "constant expressions". *)
let rec is_int_constant e =
  let open Constant in
  match e.node with
  | EConstant _ | EEnum _ | EBool _ | EUnit | EString _ | EAny ->
      true
  | ECast (e, _) ->
      is_int_constant e
  | EApp ({ node = EOp ((
        Add | AddW | Sub | SubW | Div | DivW | Mult | MultW | Mod
      | BOr | BAnd | BXor | BShiftL | BShiftR | BNot
      | Eq | Neq | Lt | Lte | Gt | Gte
      | And | Or | Xor | Not), w); _ },
    es) when w <> CInt ->
      List.for_all is_int_constant es
  | _ ->
      false

(* This is a conservative approximation. See C11 6.6. *)
let rec is_initializer_constant e =
  let is_address = function
    | TArrow _ | TBuf _ | TArray _
    (* See comment in test/TopLevelArray.fst *)
    (*| TQualified (["C";"String"], "t") *)->
        true
    | _ ->
        false
  in
  is_int_constant e ||
  match e with
  | { node = EAddrOf { node = EQualified _; _ }; _ } ->
      true
  | { node = EQualified _; typ = t } ->
      is_address t
  | { node = EEnum _; _ } ->
      true
  | { node = EString _; _ } ->
      true
  | { node = EFlat es; _ } ->
      List.for_all (fun (_, e) -> is_initializer_constant e) es
  | { node = EBufCreateL (_, es); _ } ->
      List.for_all is_initializer_constant es
  | { node = EBufCreate (_, { node = EConstant (_, "0"); _ },
                            { node = EConstant _; _ }); _ }
  | { node = EBufCreate (_, { node = EBool false; _ },
                            { node = EConstant _; _ }); _ }
  | { node = EBufCreate (_, { node = EAny; _ },
                            { node = EConstant _; _ }); _ } ->
      true
  | _ ->
      is_null e

let assert_tlid t =
  (* We only have nominal typing for variants. *)
  match t with TQualified lid -> lid | _ -> assert false

let assert_tbuf t =
  match t with TBuf (t, _) -> t | _ -> assert false

let assert_elid t =
  (* We only have nominal typing for variants. *)
  match t with EQualified lid -> lid | _ -> assert false

let assert_tbuf_or_tarray t =
  match t with
  | TBuf (t, _) | TArray (t, _) -> t
  | _ -> Warn.fatal_error "%a is neither a tbuf or tarray\n" ptyp t


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
  | ESequence es ->
      let l = List.length es in
      { node = ESequence (List.mapi (fun j e ->
          if j = l - 1 then
            nest_in_return_pos i typ f e
          else
            e
        ) es); typ }
  | _ ->
      f i e

let nest_in_return_pos = nest_in_return_pos 0

let push_ignore = nest_in_return_pos TUnit (fun _ e -> with_type TUnit (EIgnore (strip_cast e)))

(* Big AST nodes *************************************************************)

let mk_bufblit src_buf src_ofs dst_buf dst_ofs len =
  (* This function is now used for copy-assignments in C and Wasm. There are
   * some possibilities for optimization, e.g. using memset when the initial
   * value is a byte or any 0 (in C). *)
  let t = assert_tbuf_or_tarray src_buf.typ in
  match len.node with
  | EConstant (_, "1") ->
      EBufWrite (dst_buf, dst_ofs, with_type t (EBufRead (src_buf, src_ofs)))
  | _ ->
      let b_src, body_src, ref_src =
        mk_named_binding "src" (TBuf (t, true)) (EBufSub (src_buf, src_ofs))
      in
      let b_dst, body_dst, ref_dst =
        mk_named_binding "dst" (TBuf (t, false)) (EBufSub (dst_buf, dst_ofs))
      in
      let b_len, body_len, ref_len =
        mk_named_binding "len" uint32 len.node
      in
      let b_len = mark_mut b_len in
      ELet (b_src, body_src, close_binder b_src (with_unit (
      ELet (b_dst, body_dst, close_binder b_dst (with_unit (
      ELet (b_len, body_len, close_binder b_len (with_unit (
        EWhile (
          mk_gt_zero ref_len, with_unit (
          ESequence [ with_unit (
            EBufWrite (
              ref_dst,
              mk_minus_one ref_len,
              with_type t (EBufRead (ref_src, mk_minus_one ref_len)))); with_unit (
            EAssign (ref_len, mk_minus_one ref_len))])))))))))))

(* e1 := e2 *)
let mk_copy_assignment (t, size) e1 e2 =
  let assert_ro n e =
    if not (is_readonly_c_expression e) then
      Warn.fatal_error "copy-assign, %s is not a readonly expression: %a" n pexpr e
  in
  let e1 = with_type (TBuf (t, false)) e1 in
  begin match e2.node with
  | EBufCreate (_, init, len) ->
      if init.node = EAny then
        ESequence []
      else if snd size = "1" then
        (* A copy-assignment with size 1 can become a single assignment. *)
        EBufWrite (e1, zerou32, init)
      else begin
        assert_ro "e1" e1;
        let b_init = fresh_binder "init" init.typ in
        ELet (b_init, init,
          with_unit (EFor (fresh_binder ~mut:true "i" uint32,
            zerou32,
            mk_lt32 (DeBruijn.lift 2 len),
            mk_incr32,
            let i = with_type uint32 (EBound 0) in
            let init = with_type init.typ (EBound 1) in
            with_unit (EBufWrite (DeBruijn.lift 2 e1, i, init)))))
      end
  | EBufCreateL (_, inits) ->
      assert_ro "e1" e1;
      ESequence (List.mapi (fun i init -> with_unit (EBufWrite (e1, mk_uint32 i, init))) inits)
  | _ ->
      let l = with_type uint32 (EConstant size) in
      mk_bufblit e2 zerou32 e1 zerou32 l
  end
