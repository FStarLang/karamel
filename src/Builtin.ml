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

let mk_int m t =
  let mk_binop n =
    DExternal (None, ([ "FStar"; m ], n), TArrow (t, TArrow (t, t)))
  in
  let mk_op n t =
    DExternal (None, ([ "FStar"; m ], n), t)
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
    mk_op "lognot" (TArrow (t, t));
    mk_op "shift_right" (TArrow (t, TArrow (TInt UInt32, t)));
    mk_op "shift_left" (TArrow (t, TArrow (TInt UInt32, t)));
    mk_binop "eq";
    mk_binop "gt";
    mk_binop "gte";
    mk_binop "lt";
    mk_binop "lte"
  ]

let mk_builtin_int w =
  let m = string_of_width w in
  let t = TInt w in
  mk_int m t

let prims: file =
  "Prims", [
    DType ((["Prims"], "list"), [ Common.GcType ], 1, Variant [
      "Nil", [];
      "Cons", [
        "hd", (TBound 0, false);
        "tl", (TApp ((["Prims"],"list"), [ TBound 0 ]), false)
      ]
    ]);
  ]

let prelude () =
  prims ::
  List.map mk_builtin_int
    [ UInt8; UInt16; UInt32; UInt64; Int8; Int16; Int32; Int64 ]
