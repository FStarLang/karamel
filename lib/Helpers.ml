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
  | BNot | Neg ->
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

let mk_sizet i =
  with_type (TInt K.SizeT) (EConstant (K.SizeT, string_of_int i))

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
  with_type typ { name; mut; mark = ref Mark.default; meta = None; atom = Atom.fresh () }

let mark_mut b =
  { b with node = { b.node with mut = true }}

let sequence_binding () = with_type TUnit {
  name = "_";
  mut = false;
  mark = ref Mark.default;
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

(* TODO: figure this out through an attribute in the source code
   rather than a hardcoded list in krml *)
let is_aligned_type = function ["Lib"; "IntVector"; "Intrinsics"], ("vec128"|"vec256"|"vec512") -> true | _ -> false

let is_array = function TArray _ -> true | _ -> false

let is_union = function TAnonymous (Union _) -> true | _ -> false

let is_null = function
  | { node = EBufNull; _ } -> true
  | _ -> false

let is_forward = function
  | Forward _ -> true
  | _ -> false

let is_bufcreate x =
  match x.node with
  | EBufCreate _ | EBufCreateL _ -> true
  | _ -> false

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
    [ "Prims" ], "op_Minus";
    [ "Lib"; "IntVector"; "Intrinsics" ], "vec128_smul64";
    [ "Lib"; "IntVector"; "Intrinsics" ], "vec256_smul64";
    [ "FStar"; "UInt32" ], "v";
    [ "FStar"; "UInt128" ], "uint128_to_uint64";
    [ "FStar"; "UInt128" ], "uint64_to_uint128";
    [ "Eurydice" ], "vec_len";
    [ "Eurydice" ], "vec_index";
  ] in
  List.exists (fun lid' ->
    let lid = Idents.string_of_lident lid in
    let lid' = Idents.string_of_lident lid' in
    KString.starts_with lid lid'
  ) pure_builtin_lids

class ['self] closed_term_visitor = object (_: 'self)
  inherit [_] reduce
  method private zero = true
  method private plus = (&&)
  method! visit_EBound _ _ = false
  method! visit_EOpen _ _ _ = false
end

let is_closed_term = (new closed_term_visitor)#visit_expr_w ()

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
  method! visit_EMatch _ _ _ _ = false
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
    | ETApp ({ node = EQualified lid; _ }, _) when is_readonly_builtin_lid lid ->
        List.for_all (self#visit_expr_w ()) es
    | _ ->
        false
end

let is_readonly_c_expression = (new readonly_visitor)#visit_expr_w ()

let is_readonly_and_variable_free_c_expression = (object
  inherit [_] readonly_visitor
  method! visit_EBound _ _ = false
  method! visit_EOpen _ _ _ = false
end)#visit_expr_w ()


class ['self] value_visitor = object (_self: 'self)
  inherit [_] readonly_visitor
  method! visit_EApp _ _ _ = false
  method! visit_ELet _ _ _ _ = false
  method! visit_EBufRead _ _ _ = false
  method! visit_EBufSub _ _ _ = false
  method! visit_EBufDiff _ _ _ = false
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
  match t with TBuf (t, _) -> t | t -> Warn.fatal_error "Not a buffer: %a" ptyp t

let assert_tarray t =
  match t with TArray (t, _) -> t | t -> Warn.fatal_error "Not an array: %a" ptyp t

let assert_elid t =
  (* We only have nominal typing for variants. *)
  match t with EQualified lid -> lid | _ -> Warn.fatal_error "Not an equalified: %a" pexpr (with_type TAny t)

let assert_tbuf_or_tarray t =
  match t with
  | TBuf (t, _) | TArray (t, _) -> t
  | _ -> Warn.fatal_error "%a is neither a tbuf or tarray\n" ptyp t

let builtin_names =
  let known = [
    (* Built-in macro in include/krml/internal/target.h *)
    ["LowStar"; "Ignore"], "ignore";
    (* Useless definitions: they are bypassed by custom codegen. *)
    ["LowStar"; "Monotonic"; "Buffer"], "is_null";
    ["C"; "Nullity"], "is_null";
    ["LowStar"; "Monotonic"; "Buffer"], "mnull";
    ["LowStar"; "Buffer"], "null";
    ["Steel"; "Reference"], "null";
    ["Steel"; "Reference"], "is_null";
    ["Steel"; "ST"; "HigherArray"], "intro_fits_u32";
    ["Steel"; "ST"; "HigherArray"], "intro_fits_u64";
    ["Steel"; "ST"; "HigherArray"], "intro_fits_ptrdiff32";
    ["Steel"; "ST"; "HigherArray"], "intro_fits_ptrdiff64";
    ["C"; "Nullity"], "null";
    ["C"; "String"], "get";
    ["C"; "String"], "t";
    ["C"; "String"], "of_literal";
    ["C"; "Compat"; "String"], "get";
    ["C"; "Compat"; "String"], "t";
    ["C"; "Compat"; "String"], "of_literal";
    (* Trick: we typedef this as an int and reply on implicit C enum -> int
     * conversion rules. *)
    ["C"], "exit_code";
    (* These two are not integers and are macro-expanded by MingW into the
     * address of a function pointer], which would make "extern channel stdout"
     * fail. *)
    ["C"], "stdout";
    ["C"], "stderr";
    (* DLL linkage errors on MSVC. *)
    ["C"], "rand";
    ["C"], "srand";
    ["C"], "exit";
    ["C"], "fflush";
    ["C"], "clock";
    (* Special array index to turn b[0] into *b (cf. PR #278) *)
    ["C"], "_zero_for_deref";
    (* Hand-written type definition parameterized over KRML_VERIFIED_UINT128 *)
    ["FStar"; "UInt128"], "uint128";
    (* Might appear twice otherwise, which is not C89-compatible. Defined by
     * hand *)
    ["FStar"; "UInt128"], "t";
    (* Hand-written implementations in include/krml/fstar_int.h. TODO: since
     * these are now static inline, it should theoretically be ok to emit
     * definitions for them. *)
    ["FStar"; "Int8"], "shift_arithmetic_right";
    ["FStar"; "Int16"], "shift_arithmetic_right";
    ["FStar"; "Int32"], "shift_arithmetic_right";
    ["FStar"; "Int64"], "shift_arithmetic_right";
    (* Macros, no external linkage. Would be good to use static inline for some
     * amount of checking. *)
    ["C"; "Endianness"], "htole16";
    ["C"; "Endianness"], "le16toh";
    ["C"; "Endianness"], "htole32";
    ["C"; "Endianness"], "le32toh";
    ["C"; "Endianness"], "htole64";
    ["C"; "Endianness"], "le64toh";
    ["C"; "Endianness"], "htobe16";
    ["C"; "Endianness"], "be16toh";
    ["C"; "Endianness"], "htobe32";
    ["C"; "Endianness"], "be32toh";
    ["C"; "Endianness"], "htobe64";
    ["C"; "Endianness"], "be64toh";
    ["C"; "Endianness"], "store16_le";
    ["C"; "Endianness"], "load16_le";
    ["C"; "Endianness"], "store16_be";
    ["C"; "Endianness"], "load16_be";
    ["C"; "Endianness"], "store32_le";
    ["C"; "Endianness"], "load32_le";
    ["C"; "Endianness"], "store32_be";
    ["C"; "Endianness"], "load32_be";
    ["C"; "Endianness"], "load64_le";
    ["C"; "Endianness"], "store64_le";
    ["C"; "Endianness"], "load64_be";
    ["C"; "Endianness"], "store64_be";
    ["LowStar"; "Endianness"], "htole16";
    ["LowStar"; "Endianness"], "le16toh";
    ["LowStar"; "Endianness"], "htole32";
    ["LowStar"; "Endianness"], "le32toh";
    ["LowStar"; "Endianness"], "htole64";
    ["LowStar"; "Endianness"], "le64toh";
    ["LowStar"; "Endianness"], "htobe16";
    ["LowStar"; "Endianness"], "be16toh";
    ["LowStar"; "Endianness"], "htobe32";
    ["LowStar"; "Endianness"], "be32toh";
    ["LowStar"; "Endianness"], "htobe64";
    ["LowStar"; "Endianness"], "be64toh";
    ["LowStar"; "Endianness"], "store16_le";
    ["LowStar"; "Endianness"], "load16_le";
    ["LowStar"; "Endianness"], "store16_be";
    ["LowStar"; "Endianness"], "load16_be";
    ["LowStar"; "Endianness"], "store32_le";
    ["LowStar"; "Endianness"], "load32_le";
    ["LowStar"; "Endianness"], "store32_be";
    ["LowStar"; "Endianness"], "load32_be";
    ["LowStar"; "Endianness"], "load64_le";
    ["LowStar"; "Endianness"], "store64_le";
    ["LowStar"; "Endianness"], "load64_be";
    ["LowStar"; "Endianness"], "store64_be";
    ["LowStar"; "Endianness"], "store16_le_i";
    ["LowStar"; "Endianness"], "load16_le_i";
    ["LowStar"; "Endianness"], "store16_be_i";
    ["LowStar"; "Endianness"], "load16_be_i";
    ["LowStar"; "Endianness"], "store32_le_i";
    ["LowStar"; "Endianness"], "load32_le_i";
    ["LowStar"; "Endianness"], "store32_be_i";
    ["LowStar"; "Endianness"], "load32_be_i";
    ["LowStar"; "Endianness"], "load64_le_i";
    ["LowStar"; "Endianness"], "store64_le_i";
    ["LowStar"; "Endianness"], "load64_be_i";
    ["LowStar"; "Endianness"], "store64_be_i";
    (* Realized with native C arithmetic. *)
    ["FStar"; "UInt8"], "add";
    ["FStar"; "UInt8"], "add_underspec";
    ["FStar"; "UInt8"], "add_mod";
    ["FStar"; "UInt8"], "sub";
    ["FStar"; "UInt8"], "sub_underspec";
    ["FStar"; "UInt8"], "sub_mod";
    ["FStar"; "UInt8"], "mul";
    ["FStar"; "UInt8"], "mul_underspec";
    ["FStar"; "UInt8"], "mul_mod";
    ["FStar"; "UInt8"], "mul_div";
    ["FStar"; "UInt8"], "div";
    ["FStar"; "UInt8"], "rem";
    ["FStar"; "UInt8"], "logand";
    ["FStar"; "UInt8"], "logxor";
    ["FStar"; "UInt8"], "logor";
    ["FStar"; "UInt8"], "lognot";
    ["FStar"; "UInt8"], "shift_right";
    ["FStar"; "UInt8"], "shift_left";
    ["FStar"; "UInt8"], "eq";
    ["FStar"; "UInt8"], "gt";
    ["FStar"; "UInt8"], "gte";
    ["FStar"; "UInt8"], "lt";
    ["FStar"; "UInt8"], "lte";
    ["FStar"; "UInt16"], "add";
    ["FStar"; "UInt16"], "add_underspec";
    ["FStar"; "UInt16"], "add_mod";
    ["FStar"; "UInt16"], "sub";
    ["FStar"; "UInt16"], "sub_underspec";
    ["FStar"; "UInt16"], "sub_mod";
    ["FStar"; "UInt16"], "mul";
    ["FStar"; "UInt16"], "mul_underspec";
    ["FStar"; "UInt16"], "mul_mod";
    ["FStar"; "UInt16"], "mul_div";
    ["FStar"; "UInt16"], "div";
    ["FStar"; "UInt16"], "rem";
    ["FStar"; "UInt16"], "logand";
    ["FStar"; "UInt16"], "logxor";
    ["FStar"; "UInt16"], "logor";
    ["FStar"; "UInt16"], "lognot";
    ["FStar"; "UInt16"], "shift_right";
    ["FStar"; "UInt16"], "shift_left";
    ["FStar"; "UInt16"], "eq";
    ["FStar"; "UInt16"], "gt";
    ["FStar"; "UInt16"], "gte";
    ["FStar"; "UInt16"], "lt";
    ["FStar"; "UInt16"], "lte";
    ["FStar"; "UInt32"], "add";
    ["FStar"; "UInt32"], "add_underspec";
    ["FStar"; "UInt32"], "add_mod";
    ["FStar"; "UInt32"], "sub";
    ["FStar"; "UInt32"], "sub_underspec";
    ["FStar"; "UInt32"], "sub_mod";
    ["FStar"; "UInt32"], "mul";
    ["FStar"; "UInt32"], "mul_underspec";
    ["FStar"; "UInt32"], "mul_mod";
    ["FStar"; "UInt32"], "mul_div";
    ["FStar"; "UInt32"], "div";
    ["FStar"; "UInt32"], "rem";
    ["FStar"; "UInt32"], "logand";
    ["FStar"; "UInt32"], "logxor";
    ["FStar"; "UInt32"], "logor";
    ["FStar"; "UInt32"], "lognot";
    ["FStar"; "UInt32"], "shift_right";
    ["FStar"; "UInt32"], "shift_left";
    ["FStar"; "UInt32"], "eq";
    ["FStar"; "UInt32"], "gt";
    ["FStar"; "UInt32"], "gte";
    ["FStar"; "UInt32"], "lt";
    ["FStar"; "UInt32"], "lte";
    ["FStar"; "UInt64"], "add";
    ["FStar"; "UInt64"], "add_underspec";
    ["FStar"; "UInt64"], "add_mod";
    ["FStar"; "UInt64"], "sub";
    ["FStar"; "UInt64"], "sub_underspec";
    ["FStar"; "UInt64"], "sub_mod";
    ["FStar"; "UInt64"], "mul";
    ["FStar"; "UInt64"], "mul_underspec";
    ["FStar"; "UInt64"], "mul_mod";
    ["FStar"; "UInt64"], "mul_div";
    ["FStar"; "UInt64"], "div";
    ["FStar"; "UInt64"], "rem";
    ["FStar"; "UInt64"], "logand";
    ["FStar"; "UInt64"], "logxor";
    ["FStar"; "UInt64"], "logor";
    ["FStar"; "UInt64"], "lognot";
    ["FStar"; "UInt64"], "shift_right";
    ["FStar"; "UInt64"], "shift_left";
    ["FStar"; "UInt64"], "eq";
    ["FStar"; "UInt64"], "gt";
    ["FStar"; "UInt64"], "gte";
    ["FStar"; "UInt64"], "lt";
    ["FStar"; "UInt64"], "lte";
  ] in
  let h = Hashtbl.create 41 in
  List.iter (fun s -> Hashtbl.add h s ()) known;
  h

(* Builtin names, meaning we don't generate declarations for them *)
let is_primitive s =
  Hashtbl.mem builtin_names s ||
  match s with
  | ["C"; "Nullity"], s when KString.starts_with s "op_Bang_Star__" ->
      true
  | ["LowStar"; "BufferOps"], s when KString.starts_with s "op_Bang_Star__" ->
      true
  | ["LowStar"; "BufferOps"], s when KString.starts_with s "op_Star_Equals__" ->
      true
  | _ ->
      false

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
  | EMatch (c, e, branches) ->
      { node =
        EMatch (c, e, List.map (fun (bs, p, e) ->
          bs, p, nest_in_return_pos (i + List.length bs) typ f e
        ) branches);
        typ }
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

let push_ignore = nest_in_return_pos TUnit (fun _ e ->
  with_type TUnit (EApp (
    with_type (TArrow (e.typ, TUnit)) (
      ETApp (
        with_type (TArrow (TBound 0, TUnit))
          (EQualified (["LowStar"; "Ignore"], "ignore")),
        [ e.typ ]
      )),
    [ e ])))

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
