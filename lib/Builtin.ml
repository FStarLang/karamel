(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Removing all traces of F* models and replacing them with built-in
 * definitions or abstract ones before re-checking the program as Low*. *)

open Ast
open Helpers

let t_string = TQualified (["Prims"], "string")

let mk_binop m n t =
  DExternal (None, [ ], 0, 0, (m, n), TArrow (t, TArrow (t, t)), [ "x"; "y" ])

let mk_val ?(flags=[]) ?(nvars=0) m n t =
  DExternal (None, flags, 0, nvars, (m, n), t, [])

let prims: file =
  let t = TInt K.CInt in
  let mk_binop n = mk_binop [ "Prims" ] n t in
  let mk_boolop n = mk_val [ "Prims" ] n (TArrow (t, TArrow (t, TBool))) in
  let mk_unop n = mk_val [ "Prims" ] n (TArrow (t, t)) in
  let mk_val = mk_val [ "Prims" ] in
  let dtuple10 = TApp ((["Prims"],"dtuple2"), [ TBound 1; TBound 0 ]) in
  "Prims", [
    DType ((["Prims"], "list"), [ Common.GcType ], 0, 1, Variant [
      "Nil", [];
      "Cons", [
        "hd", (TBound 0, false);
        "tl", (TApp ((["Prims"],"list"), [ TBound 0 ]), false)
      ]
    ]);
    DType ((["Prims"], "dtuple2"), [], 0, 2, Variant [
      "Mkdtuple2", [
        "fst", (TBound 1, false);
        "snd", (TBound 0, false)
      ]
    ]);
    DFunction (None,
      [ Common.Private ], 0, 2, TBound 1,
      (["Prims"], "__proj__Mkdtuple2__item___1"),
      [ fresh_binder "pair" dtuple10 ],
      (* match pair with *)
      with_type (TBound 1) (EMatch (Checked, with_type dtuple10 (EBound 0), [
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
      [ Common.Private ], 0, 2, TBound 0,
      (["Prims"], "__proj__Mkdtuple2__item___2"),
      [ fresh_binder "pair" dtuple10 ],
      (* match pair with *)
      with_type (TBound 0) (EMatch (Checked, with_type dtuple10 (EBound 0), [
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
    mk_unop "op_Minus";
    mk_binop "op_Modulus";
    mk_boolop "op_LessThanOrEqual";
    mk_boolop "op_GreaterThan";
    mk_boolop "op_GreaterThanOrEqual";
    mk_boolop "op_LessThan";
    mk_unop "pow2";
    mk_unop "abs";
    mk_val "strcat" (TArrow (t_string, TArrow (t_string, t_string)));
    mk_val "string_of_int" (TArrow (TInt K.CInt, t_string));
    DType ((["Prims"], "prop"), [], 0, 0, Abbrev TUnit);
    DType ((["Prims"], "nat"), [ Common.Private ], 0, 0, Abbrev (TQualified (["Prims"], "int")))
  ]

(* JP: as a guiding principle: builtins that are from LowStar.Monotonic.Buffer
 * are not aware of any const qualifier (only LowStar.ConstBuffer does), so
 * let's not bother with putting const qualifiers on those signatures -- most of
 * them will be eliminated anyhow.
 *
 * We make an exception for eqb below in the hope that this triggers more
 * optimizations for the compiler? *)

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
    DFunction (None, [ ], 0, 1, TBool, ([ "FStar"; "Buffer" ], "eqb"),
      [ fresh_binder "b1" (TBuf (TBound 0, true));
        fresh_binder "b2" (TBuf (TBound 0, true));
        fresh_binder "len" uint32 ],
      with_type TBool (ELet (fresh_binder ~mut:true "ret" TBool, etrue,
      with_type TBool (ESequence [
      with_unit (EFor (fresh_binder ~mut:true "i" uint32, zerou32,
        mk_lt32 (with_type uint32 (EBound 2)),
        mk_incr32,
        with_unit (EIfThenElse (with_type TBool (
          EApp (with_type (TArrow (TBound 0, TArrow (TBound 0, TBool)))
            (EPolyComp (K.PNeq, TBound 0)), [
            with_type (TBound 0) (EBufRead (
              with_type (TBuf (TBound 0, true)) (EBound 3),
              with_type uint32 (EBound 0)));
            with_type (TBound 0) (EBufRead (
              with_type (TBuf (TBound 0, true)) (EBound 4),
              with_type uint32 (EBound 0)))])),
          with_unit (ESequence [
            with_unit (EAssign (with_type TBool (EBound 1), efalse));
            with_unit EBreak ]),
          eunit))));
      with_type TBool (EBound 0)]))));

    DFunction (None, [ Common.MustDisappear ], 0, 1, TUnit,
      ([ "FStar"; "Buffer" ], "recall"),
      [ fresh_binder "x" (TBuf (TBound 0, true)) ],
      eunit);
  ]

let monotonic_hs: file =
  "FStar_Monotonic_HyperStack", [
    DType (([ "FStar"; "Monotonic"; "HyperStack" ], "mem"), [], 0, 0, Abbrev TUnit);
    DGlobal ([], ([ "FStar"; "Monotonic"; "HyperStack" ], "root"), 0, TUnit, eunit);
  ]

let monotonic_hh: file =
  "FStar_Monotonic_HyperHeap", [
    DType (([ "FStar"; "Monotonic"; "HyperHeap" ], "rid"), [], 0, 0, Abbrev TUnit)
  ]

let hs: file =
  "FStar_HyperStack_ST", [
    DFunction (None, [ Common.MustDisappear ], 0, 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "new_region"),
      [ fresh_binder "x" TUnit ],
      with_unit (EBound 0));
    DFunction (None, [ Common.MustDisappear ], 0, 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "new_colored_region"),
      [ fresh_binder "x" TUnit; fresh_binder "x" (TInt K.CInt) ],
      with_unit (EBound 1));
    DFunction (None, [ Common.MustDisappear ], 0, 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "recall"),
      [ fresh_binder "x" TAny ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "testify"),
      [ fresh_binder "x" TAny ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "testify_forall"),
      [ fresh_binder "x" TAny ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "testify_forall_region_contains_pred"),
      [ fresh_binder "x" TAny;
        fresh_binder "y" TAny ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "recall_region"),
      [ fresh_binder "x" TUnit ],
      with_unit (EBound 0));
    DFunction (None, [ Common.MustDisappear ], 0, 0, TUnit,
      ([ "FStar"; "HyperStack"; "ST" ], "mr_witness"),
      [
        fresh_binder "x" TUnit;
        fresh_binder "x" TUnit;
        fresh_binder "x" TUnit;
        fresh_binder "x" (TBuf (TAny, false));
        fresh_binder "x" TUnit;
      ],
      eunit);
    DType (([ "FStar"; "HyperStack"; "ST" ], "erid"), [], 0, 0, Abbrev TUnit);
    DType (([ "FStar"; "HyperStack"; "ST" ], "ex_rid"), [], 0, 0, Abbrev TUnit);
    DType (([ "FStar"; "HyperStack"; "ST" ], "witnessed"), [ Common.MustDisappear ], 0, 1, Abbrev TUnit);
  ]

let dyn: file =
  let void_star = TBuf (TAny, false) in
  "FStar_Dyn", [
    DFunction (None, [], 0, 1, void_star,
      ([ "FStar"; "Dyn" ], "mkdyn"),
      [ fresh_binder "x" (TBound 0) ],
      with_type void_star (ECast (with_type (TBound 0) (EBound 0), void_star)))
  ]

let steel_sizet_intros : file =
  "Steel_ST_HigherArray", [
    mk_val ["Steel"; "ST"; "HigherArray" ] "intro_fits_u32" (TArrow (TUnit, TUnit));
    mk_val ["Steel"; "ST"; "HigherArray" ] "intro_fits_u64" (TArrow (TUnit, TUnit));
    mk_val ["Steel"; "ST"; "HigherArray" ] "intro_fits_ptrdiff32" (TArrow (TUnit, TUnit));
    mk_val ["Steel"; "ST"; "HigherArray" ] "intro_fits_ptrdiff64" (TArrow (TUnit, TUnit));
  ]

let steel_arrayarith : file =
  "Steel_ArrayArith", [
    mk_val ["Steel"; "ArrayArith"] "within_bounds_ptr"
      (TArrow
        (* The three permissions, extracted to unit *)
        (TUnit, TArrow (TUnit, TArrow (TUnit,
        (* The three arrays passed as arguments *)
        TArrow (TBuf (TAny, false), TArrow (TBuf (TAny, false), TArrow (TBuf (TAny, false),
        (* The three ghost lengths, extracted to unit *)
        TArrow (TUnit, TArrow (TUnit, TArrow (TUnit,
        (* The three ghost sequences, extracted to unit *)
        TArrow (TUnit, TArrow (TUnit, TArrow (TUnit,
        (* The actual return type *)
        TBool)))))))))))))
  ]

let lowstar_monotonic_buffer: file =
  "LowStar_Monotonic_Buffer", [
    DFunction (None, [ Common.MustDisappear ], 0, 3, TUnit,
      ([ "LowStar"; "Monotonic"; "Buffer" ], "recall"),
      [ fresh_binder "x" (TBuf (TBound 2, false)) ],
      eunit);
    DFunction (None, [ Common.MustDisappear ], 0, 3, TUnit,
      ([ "LowStar"; "Monotonic"; "Buffer" ], "frameOf"),
      [ fresh_binder "x" (TBuf (TBound 2, false)) ],
      eunit);
    DType (([ "LowStar"; "Monotonic"; "Buffer" ], "loc_disjoint"), [ Common.MustDisappear ], 0, 2, Abbrev TUnit);
  ]

let lowstar_buffer: file =
  "LowStar_Buffer", [
    mk_val [ "LowStar"; "Buffer" ] "null" (TArrow (TAny, TBuf (TAny, false)));
  ]

let lowstar_ignore: file =
  "LowStar_Ignore", [
    mk_val ~nvars:1 [ "LowStar"; "Ignore" ] "ignore" (TArrow (TBound 0, TUnit))
  ]

let lowstar_endianness: file =
  let open Constant in
  let buf8 = TBuf (TInt UInt8, false) in
  let int32 = TInt UInt32 in
  (* In the model, store depends on store_i; however, at run-time, we define store
   * and store_i is just an alias for store along with a buffer offset. *)
  let mk t e =
    let bw = match t with
      | TInt w -> bytes_of_width w * 8
      | TQualified (["FStar"; "UInt128"], "uint128") -> 128
      | _ -> assert false
    in
    let store_t = TArrow (buf8, TArrow (t, TUnit)) in
    let store_lid = [ "LowStar"; "Endianness" ], KPrint.bsprintf "store%d_%s" bw e in
    let store_i_lid = [ "LowStar"; "Endianness" ], KPrint.bsprintf "store%d_%s_i" bw e in
    [
      (* assume val store16_le: buffer uint8 -> uint16 -> unit *)
      mk_val (fst store_lid) (snd store_lid) store_t;
      (* let store16_le_i #_ #_ b i x = store16_le (b + i) x *)
      DFunction (None, [ Common.MustDisappear ], 0, 2, TUnit,
      store_i_lid,
      [ fresh_binder "b" buf8; fresh_binder "i" int32; fresh_binder "x" t ],
      with_unit (EApp (with_type store_t (EQualified store_lid),
        [ with_type buf8 (EBufSub (with_type buf8 (EBound 2), with_type int32 (EBound 1)));
          with_type t (EBound 0) ])));
    ]

    @

    let load_t = TArrow (buf8, t) in
    let load_lid = [ "LowStar"; "Endianness" ], KPrint.bsprintf "load%d_%s" bw e in
    let load_i_lid = [ "LowStar"; "Endianness" ], KPrint.bsprintf "load%d_%s_i" bw e in
    [
      (* assume val load16_le: buffer uint8 -> uint16 *)
      mk_val (fst load_lid) (snd load_lid) load_t;
      (* let load16_le_i #_ #_ b i = load16_le (b + i) *)
      DFunction (None, [ Common.MustDisappear ], 0, 2, t,
      load_i_lid,
      [ fresh_binder "b" buf8; fresh_binder "i" int32 ],
      with_type t (EApp (with_type load_t (EQualified load_lid),
        [ with_type buf8 (EBufSub (with_type buf8 (EBound 1), with_type int32 (EBound 0)))])));
    ]
  in
  let mk_conv s t = [
    mk_val [ "LowStar"; "Endianness" ] ("hto" ^ s) (TArrow (TInt t, TInt t));
    mk_val [ "LowStar"; "Endianness" ] (s ^ "toh") (TArrow (TInt t, TInt t))
  ] in
  "LowStar_Endianness",
  mk (TInt UInt16) "le" @
  mk (TInt UInt16) "be" @
  mk (TInt UInt32) "le" @
  mk (TInt UInt32) "be" @
  mk (TInt UInt64) "le" @
  mk (TInt UInt64) "be" @
  mk (TQualified (["FStar"; "UInt128"], "uint128")) "le" @
  mk (TQualified (["FStar"; "UInt128"], "uint128")) "be" @
  mk_conv "le16" UInt16 @
  mk_conv "le32" UInt32 @
  mk_conv "le64" UInt64 @
  mk_conv "be16" UInt16 @
  mk_conv "be32" UInt32 @
  mk_conv "be64" UInt64


let c_nullity: file =
  (* Poor man's substitute to polymorphic assumes ... this needs to be here to
   * provide proper typing when is_null is in match position. *)
  "C_Nullity", [
    mk_val [ "C"; "Nullity" ] "is_null" (TArrow (TBuf (TAny, false), TBool));
    mk_val [ "C"; "Nullity" ] "null" (TArrow (TAny, TBuf (TAny, false)))
  ]

let lib_memzero0: file =
  "Lib_Memzero0", [
    mk_val ~nvars:1 [ "Lib"; "Memzero0" ] "memzero" (TArrow (TBuf (TBound 0, false), TArrow (TInt UInt32, TUnit)))
  ]

let c_deref: file =
  "C", [
    mk_val ["C"] "_zero_for_deref" (TInt UInt32)
  ]

(* These modules are entirely written by hand in abstract syntax. *)
let hand_written = [
  buffer;
  lowstar_monotonic_buffer;
  lowstar_buffer;
  lowstar_ignore;
  lowstar_endianness;
  monotonic_hh;
  monotonic_hs;
  steel_arrayarith;
  steel_sizet_intros;
  hs;
  dyn;
]

(* These modules get a couple bonus definitions. *)
let addendum = [
  c_nullity;
  lib_memzero0;
]

let make_abstract_function_or_global = function
  | DFunction (cc, flags, n_cgs, n, t, name, bs, _) ->
      let t = fold_arrow (List.map (fun b -> b.typ) bs) t in
      if n = 0 || !Options.allow_tapps then
        Some (DExternal (cc, flags, n_cgs, n, name, t, List.map (fun x -> x.node.name) bs))
      else
        None
  | DGlobal (flags, name, n, t, body) when not (List.mem Common.Macro flags) ->
      let open PrintAst.Ops in
      (* So it's pretty frustrating to have to pattern-match on expressions that we know will be
         simplified later. But sadly, -library'ing must happen very early on, as successful bundling
         depends on those definitions being made abstract. This is why we can't run this
         per-definition, at a later phase, where e.g. simplify0 would've run and would relieve us of
         having to do these silly pattern-matches. *)
      if n = 0 then
        let t =
          match t, body.node with
          | TBuf (t, _), (EBufCreateL (_, l) | ELet (_, { node = EBufCreateL (_, l); _ }, { node = EBound 0; _ })) ->
              TArray (t, (K.Int32, string_of_int (List.length l)))
          | TBuf (t, _), (EBufCreate (_, _, size) | ELet (_, { node = EBufCreate (_, _, size); _ }, { node = EBound 0; _ })) ->
              begin match size.node with
              | EConstant k ->
                  TArray (t, k)
              | _ ->
                  (* TODO: use a special encoding (e.g. max_int) to produce
                     extern int x[]; *)
                  Warn.fatal_error "-library on %a which has non-constant array length" plid name
              end
          | TBuf _, _ ->
              (* Since this phase runs quite early, the goal is to make sure
                 that we can safely assess whether this needs to have a storage
                 type or a pointer type. (These don't link the same! See #130). *)
              if not (Helpers.is_initializer_constant body) then
                Warn.maybe_fatal_error ("", LibraryPointerAmbiguity (name, body));
              t
          | _ ->
              t
        in
        Some (DExternal (None, flags, 0, 0, name, t, []))
      else
        None
  | DType (name, flags, _, _, _) when List.mem Common.AbstractStruct flags ->
      (* We assume the module doesn't lie and the CAbstractStruct will type-check in C. *)
      Some (DType (name, List.filter ((<>) Common.AbstractStruct) flags, 0, 0, Forward FStruct))
  | d ->
      Some d

(* Transforms an F*-provided machine integer module into an abstract version
 * where:
 * - the model of a machine integer as an inductive is gone
 * - operators (marked as unfold) are gone
 * - lets are replaced by vals
 * - but we keep the gte_mask and eq_mask functions *)
let make_abstract (name, decls) =
  name, List.filter_map (function
    | DType (_, _, _, _, Abbrev _) as t ->
        Some t
    | DType _ ->
        None
    | DGlobal (_, name, _, _, _) when KString.starts_with (snd name) "op_" ->
        None
    | d ->
        match lid_of_decl d with
        | [ "FStar"; _ ], ("eq_mask" | "gte_mask") when !Options.extract_uints ->
            Some d
        | _ ->
            make_abstract_function_or_global d
  ) decls

let is_model name =
  let is_machine_integer name =
    (KString.starts_with name "FStar_UInt" ||
      KString.starts_with name "FStar_Int") &&
    name <> "FStar_UInt" && name <> "FStar_Int" && name <> "FStar_Int_Cast_Full"
  in
  if name = "FStar_UInt128" then
    not (!Options.extract_uints)
  else
    is_machine_integer name ||
    List.mem name [
      "C_String";
      "C_Compat_String";
      "FStar_String";
      "Steel_SpinLock"
    ] || (
      Options.rust () &&
      List.mem name [
        "Pulse_Lib_Slice"
      ]
    )

(* We have several different treatments. *)
let prepare files =
  (* prims is a special-case, as it is not extracted by F* (FIXME) *)
  prims :: List.map (fun f ->
    let name = fst f in
    (* machine integers, some modules from the C namespace just become abstract in Low*. *)
    let f = if is_model name then make_abstract f else f in
    try
      (* some modules (e.g. ST) are entirely written by hand since we only care
       * about a couple definitions anyhow. *)
      name, List.assoc name hand_written
    with Not_found ->
      try
        (* some modules need extra definitions appended (mostly for polymorphic
         * assume val's, like C.exit) *)
        let extra = List.assoc name addendum in
        name, snd f @ extra
      with Not_found ->
        f
  ) files @
  (* This is unfortunately needed because of PR #278, and especially the corresponding
     F* PR: References to module C can now occur even when the module is not in the scope.
     If so, we add the definition that is needed as a builtin, since it will be rewritten
     during C code generation *)
  (if List.mem_assoc "C" files then [] else [c_deref]) @
  (if List.mem_assoc "LowStar_Ignore" files then [] else [lowstar_ignore]) @
  []

let make_library (name, decls) =
  name, List.filter_map make_abstract_function_or_global decls

(* Transforms declarations covered by -library into a set of "assume val" that
 * will generate proper "extern" declarations in C. *)
let make_libraries =
  List.map (fun f ->
    if List.exists (fun p -> Bundle.pattern_matches_file p (fst f)) !Options.library then
      make_library f
    else
      f)
