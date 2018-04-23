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

let t_string = TQualified (["Prims"], "string")

let mk_binop m n t =
  DExternal (None, [ Common.Private ], (m, n), TArrow (t, TArrow (t, t)))

let mk_val m n t =
  DExternal (None, [ Common.Private ], (m, n), t)

let mk_int m t =
  let mk_binop n =
    mk_binop [ "FStar"; m ] n t
  in
  let mk_val n t =
    mk_val [ "FStar"; m ] n t
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
    mk_val "lognot" (TArrow (t, t));
    mk_val "shift_right" (TArrow (t, TArrow (TInt UInt32, t)));
    mk_val "shift_left" (TArrow (t, TArrow (TInt UInt32, t)));
    mk_binop "eq";
    mk_binop "gt";
    mk_binop "gte";
    mk_binop "lt";
    mk_binop "lte";
    mk_binop "gte_mask";
    mk_binop "eq_mask";
    mk_val "to_string" (TArrow (t, t_string));
    mk_val "v" (TArrow (t, TInt K.CInt));
    mk_val "uint_to_t" (TArrow (TInt K.CInt, t))
  ]

let mk_builtin_int w =
  let m = string_of_width w in
  let t = TInt w in
  mk_int m t

let prims: file =
  let t = TInt K.CInt in
  let mk_binop n = mk_binop [ "Prims" ] n t in
  let mk_boolop n = mk_val [ "Prims" ] n (TArrow (t, TArrow (t, TBool))) in
  let mk_unop n = mk_val [ "Prims" ] n (TArrow (t, t)) in
  let mk_val = mk_val [ "Prims" ] in
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
    mk_unop "pow2";
    mk_val "strcat" (TArrow (t_string, TArrow (t_string, t_string)));
    mk_val "string_of_int" (TArrow (TInt K.CInt, t_string))
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
      with_type TBool (EBound 0)]))));
    
    DFunction (None, [ Common.MustDisappear ], 1, TUnit,
      ([ "FStar"; "Buffer" ], "recall"),
      [ fresh_binder "x" (TBuf (TBound 0)) ],
      eunit);
  ]

let monotonic_hh: file =
  "FStar_Monotonic_HyperHeap", [
    DType (([ "FStar"; "Monotonic"; "HyperHeap" ], "rid"), [], 0, Abbrev TUnit)
  ]

let hs: file =
  "FStar_HyperStack_ST", [
    DFunction (None, [ Common.MustDisappear ], 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "new_region"),
      [ fresh_binder "x" TUnit ],
      with_unit (EBound 0));
    DFunction (None, [ Common.MustDisappear ], 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "new_colored_region"),
      [ fresh_binder "x" TUnit; fresh_binder "x" (TInt K.CInt) ],
      with_unit (EBound 1));
    DFunction (None, [ Common.MustDisappear ], 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "recall"),
      [ fresh_binder "x" TAny ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "testify"),
      [ fresh_binder "x" TAny ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "testify_forall"),
      [ fresh_binder "x" TAny ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "testify_forall_region_contains_pred"),
      [ fresh_binder "x" TAny;
        fresh_binder "y" TAny ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "recall_region"),
      [ fresh_binder "x" TUnit ],
      with_unit (EBound 0));
    DFunction (None, [ Common.MustDisappear ], 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "mr_witness"),
      [
        fresh_binder "x" TUnit;
        fresh_binder "x" TUnit;
        fresh_binder "x" TUnit;
        fresh_binder "x" (TBuf TAny);
        fresh_binder "x" TUnit;
      ],
      eunit);
    DType (([ "FStar"; "HyperStack"; "ST" ], "erid"), [], 0, Abbrev TUnit);
    DType (([ "FStar"; "HyperStack"; "ST" ], "rid"), [], 0, Abbrev TUnit);
  ]

let dyn: file =
  let void_star = TBuf TAny in
  "FStar_Dyn", [
    DFunction (None, [], 1, void_star,
      ([ "FStar"; "Dyn" ], "mkdyn"),
      [ fresh_binder "x" (TBound 0) ],
      with_type void_star (ECast (with_type (TBound 0) (EBound 0), void_star)))
  ]

let c_string: file =
  let t = TQualified ([ "C"; "String" ], "t") in
  "C_String", [
    mk_val [ "C"; "String" ] "print" (TArrow (t, TUnit))
  ]

let c: file =
  "C", [
    mk_val [ "C" ] "exit" (TArrow (TInt K.Int32, TUnit))
  ]

let prelude () =
  prims ::
  List.map mk_builtin_int
    [ UInt8; UInt16; UInt32; UInt64; Int8; Int16; Int32; Int64 ] @ [
  buffer;
  monotonic_hh;
  hs;
  dyn;
  c_string;
  c ] @ (
    let t = TQualified (["FStar"; "UInt128"], "uint128") in
    let augment prelude (filename, decls) = filename, prelude @ decls in
    let default =
      [
        DExternal (None, [], (["FStar"; "UInt128"], "uint64_to_uint128"),
          (TArrow (TInt UInt64, t)));
        DExternal (None, [], (["FStar"; "UInt128"], "uint128_to_uint64"),
          (TArrow (t, TInt UInt64)));
        DType (([ "FStar"; "UInt128"], "t"), [], 0, Abbrev t);
      ]
    in
    if !Options.uint128 then
      [ augment default (mk_int "UInt128" t) ]
    else
      [ "FStar_UInt128", default ]
  )

let nullity: decl list =
  (* Poor man's substitute to polymorphic assumes ... this needs to be here to
   * provide proper typing when is_null is in match position. *)
  [
    mk_val [ "C"; "Nullity" ] "is_null" (TArrow (TBuf TAny, TBool));
    mk_val [ "C"; "Nullity" ] "null" (TArrow (TAny, TBuf TAny))
  ]

let augment files =
  List.map (function
    | "C_Nullity", decls -> "C_Nullity", decls @ nullity
    | f -> f
  ) files
