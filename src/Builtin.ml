(** Builtin module declarations. We want to hand-roll some definitions for two
   reasons:
   - most of the module doesn't make sense in Low* (e.g. Prims), so rather than
     spew a bunch of warnings, we just redefine the list type
   - the module is a model in F*, but not in Low*; this is the case of all the
     machine integer modules; they're defined in F* using an inductive, but we
     don't want a struct definition to be generated in Low*, so we swap them
     with a bunch of assumed definitions over the built-in fixed-width types. *)

open Ast
open Constant
open Helpers

let string_of_width = function
  | UInt8 -> "UInt8"
  | UInt16 -> "UInt16"
  | UInt32 -> "UInt32"
  | UInt64 -> "UInt64"
  | Int8 -> "Int8"
  | Int16 -> "Int16"
  | Int32 -> "Int32"
  | Int64 -> "Int64"
  | _ -> invalid_arg "string_of_width"

let mk_binop m n t =
  DExternal (None, [], (m, n), TArrow (t, TArrow (t, t)))

let mk_unop m n t =
  DExternal (None, [], (m, n), t)

let mk_int m t =
  let mk_binop n =
    mk_binop [ "FStar"; m ] n t
  in
  let mk_unop n t =
    mk_unop [ "FStar"; m ] n t
  in
  let mk_binops n =
    [ mk_binop n; mk_binop (n ^ "_mod"); mk_binop (n ^ "_underspec") ]
  in
  "FStar_" ^ m,
  mk_binops "add" @
  mk_binops "sub" @
  mk_binops "mul" @ [
    mk_binop "div";
    mk_binop "div_underspec";
    mk_binop "rem";
    mk_binop "logand";
    mk_binop "logxor";
    mk_binop "logor";
    mk_unop "lognot" (TArrow (t, t));
    mk_unop "shift_right" (TArrow (t, TArrow (TInt UInt32, t)));
    mk_unop "shift_left" (TArrow (t, TArrow (TInt UInt32, t)));
    mk_binop "eq";
    mk_binop "gt";
    mk_binop "gte";
    mk_binop "lt";
    mk_binop "lte";
    mk_unop "to_string" (TArrow (t, TQualified (["Prims"],"string")));
    mk_unop "v" (TArrow (t, TInt K.CInt));
    mk_unop "uint_to_t" (TArrow (TInt K.CInt, t))
  ]

let mk_builtin_int w =
  let m = string_of_width w in
  let t = TInt w in
  mk_int m t

let prims: file =
  let t = TInt K.CInt in
  let mk_binop n = mk_binop [ "Prims" ] n t in
  let mk_boolop n = mk_unop [ "Prims" ] n (TArrow (t, TArrow (t, TBool))) in
  let mk_unop n = mk_unop [ "Prims" ] n (TArrow (t, t)) in
  let dtuple10 = TApp ((["Prims"],"dtuple2"), [ TBound 1; TBound 0 ]) in
  "Prims", [
    DType ((["Prims"], "list"), [ Common.GcType ], 1, Variant [
      "Nil", [];
      "Cons", [
        "hd", (TBound 0, false);
        "tl", (TApp ((["Prims"],"list"), [ TBound 0 ]), false)
      ]
    ]);
    DType ((["Prims"], "dtuple2"), [], 2, Variant [
      "Mkdtuple2", [
        "fst", (TBound 1, false);
        "snd", (TBound 0, false)
      ]
    ]);
    DFunction (None,
      [ Common.Private ], 2, TBound 1,
      (["Prims"], "__proj__Mkdtuple2__item___1"),
      [ fresh_binder "pair" dtuple10 ],
      (* match pair with *)
      with_type (TBound 1) (EMatch (with_type dtuple10 (EBound 0), [
        (* \ fst *)
        [ fresh_binder "fst" (TBound 1) ],
        (* Mkdtuple2 (fst, _) *)
        with_type dtuple10 (PCons ("Mkdtuple2", [
          with_type (TBound 1) (PBound 0);
          with_type TAny PWild
        ])),
        (* -> fst *)
        with_type (TBound 1) (EBound 0)
      ])));
    DFunction (None,
      [ Common.Private ], 2, TBound 0,
      (["Prims"], "__proj__Mkdtuple2__item___2"),
      [ fresh_binder "pair" dtuple10 ],
      (* match pair with *)
      with_type (TBound 0) (EMatch (with_type dtuple10 (EBound 0), [
        (* \ snd *)
        [ fresh_binder "snd" (TBound 0) ],
        (* Mkdtuple2 (_, snd) *)
        with_type dtuple10 (PCons ("Mkdtuple2", [
          with_type TAny PWild;
          with_type (TBound 0) (PBound 0)
        ])),
        (* -> snd *)
        with_type (TBound 0) (EBound 0)
      ])));
    mk_binop "op_Multiply";
    mk_binop "op_Division";
    mk_binop "op_Subtraction";
    mk_binop "op_Addition";
    mk_binop "op_Minus";
    mk_binop "op_Modulus";
    mk_boolop "op_LessThanOrEqual";
    mk_boolop "op_GreaterThan";
    mk_boolop "op_GreaterThanOrEqual";
    mk_boolop "op_LessThan";
    mk_unop "pow2"
  ]

let buffer: file =
  "FStar_Buffer", [
    (* let eqb #a b1 b2 len =
     *   let mut ret = true in
     *   for let mut i = 0; i < len; i <- i + 1
     *     if ((<>) (a -> a -> bool) b1[i] b2[i])
     *       ret <- false
     *       break
     *   ret
     *)
    DFunction (None, [ Common.Private ], 1, TBool, ([ "FStar"; "Buffer" ], "eqb"),
      [ fresh_binder "b1" (TBuf (TBound 0));
        fresh_binder "b2" (TBuf (TBound 0));
        fresh_binder "len" uint32 ],
      with_type TBool (ELet (fresh_binder ~mut:true "ret" TBool, etrue,
      with_type TBool (ESequence [
      with_unit (EFor (fresh_binder ~mut:true "i" uint32, zerou32,
        mk_lt32 (with_type uint32 (EBound 2)),
        mk_incr32,
        with_unit (EIfThenElse (with_type TBool (
          EApp (with_type (TArrow (TBound 0, TArrow (TBound 0, TBool)))
            (ETApp (with_type (TArrow (TBound 0, TArrow (TBound 0, TBool)))
              (EOp (K.Neq, K.Bool)),
              [ TBound 0 ])), [
            with_type (TBound 0) (EBufRead (
              with_type (TBuf (TBound 0)) (EBound 3),
              with_type uint32 (EBound 0)));
            with_type (TBound 0) (EBufRead (
              with_type (TBuf (TBound 0)) (EBound 4),
              with_type uint32 (EBound 0)))])),
          with_unit (ESequence [
            with_unit (EAssign (with_type TBool (EBound 1), efalse));
            with_unit EBreak ]),
          eunit))));
      with_type TBool (EBound 0)]))))
  ]

let monotonic_hh: file =
  "FStar_Monotonic_HyperHeap", [
    DType (([ "FStar"; "Monotonic"; "HyperHeap" ], "rid"), [], 0, Abbrev TUnit)
  ]

let hs: file =
  "FStar_HyperStack_ST", [
    DFunction (None, [ Common.Private; Common.Substitute ], 0, TUnit,
    ([ "FStar"; "HyperStack"; "ST" ], "new_region"),
    [ fresh_binder "x" TUnit ],
    with_unit (EBound 0))]

let prelude () =
  prims ::
  List.map mk_builtin_int
    [ UInt8; UInt16; UInt32; UInt64; Int8; Int16; Int32; Int64 ] @ [
  buffer;
  monotonic_hh;
  hs ]

let nullity: decl list =
  (* Poor man's substitute to polymorphic assumes ... this needs to be here to
   * provide proper typing when is_null is in match position. *)
  [
    mk_unop [ "C"; "Nullity" ] "is_null" (TArrow (TBuf TAny, TBool))
  ]

let augment files =
  List.map (function
    | "C_Nullity", decls -> "C_Nullity", decls @ nullity
    | f -> f
  ) files
