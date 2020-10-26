(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

open CFlat
open CFlat.Sizes
open Loc

module W = Wasm
module K = Constant

module StringMap = Map.Make(String)

(******************************************************************************)
(* Environments                                                               *)
(******************************************************************************)

type env = {
  funcs: int StringMap.t;
    (** Mapping each function to its index in the function index space. *)
  globals: int StringMap.t;
    (** Mapping each global to its index in the global index space. *)
  n_args: int;
    (** The number of arguments to the current function. Needed to compute the
     * index of the four "scratch" variables that each function has (see dup32). *)
  strings: (string, int) Hashtbl.t;
    (** Mapping constant string literals to their offset relative to the start
     * of THIS module's data segment. *)
  data_size: int ref;
    (** The current size of THIS module's data segment. This field and the one
     * above are mutable, so as to lazily allocate string literals as we hit
     * them. *)
  location: loc list;
    (** For debugging *)
}

let empty = {
  funcs = StringMap.empty;
  globals = StringMap.empty;
  n_args = 0;
  strings = Hashtbl.create 41;
  data_size = ref 0;
  location = []
}

let debug m { globals; funcs; _ } =
  KPrint.bprintf "===== WASM DEBUG for %s =====\n" m;
  StringMap.iter (fun f i -> KPrint.bprintf "Function $%d is %s\n" i f) funcs;
  StringMap.iter (fun g i -> KPrint.bprintf "Global $%d is %s\n" i g) globals;
  KPrint.bprintf "\n\n"

let locate env loc =
  { env with location = update_location env.location loc }

let find_global env name =
  try
    StringMap.find name env.globals
  with Not_found ->
    Warn.fatal_error "Could not resolve global %s (look out for Warning 12)" name

let name_of_string = W.Utf8.decode
let string_of_name = W.Ast.string_of_name

let rec find_func env name =
  try
    StringMap.find name env.funcs
  with Not_found ->
    Warn.fatal_error "%a: Could not resolve function %s" ploc env.location name

let primitives = [
  "load32_le";
  "load32_be";
  "load64_le";
  "load64_be";
  "load128_le";
  "load128_be";
  "store32_le";
  "store32_be";
  "store64_le";
  "store64_be";
  "store128_le";
  "store128_be";
  "load32_le_i";
  "load32_be_i";
  "load64_le_i";
  "load64_be_i";
  "load128_le_i";
  "load128_be_i";
  "store32_le_i";
  "store32_be_i";
  "store64_le_i";
  "store64_be_i";
  "store128_le_i";
  "store128_be_i";
]

let is_primitive x =
  List.mem x primitives


(******************************************************************************)
(* Helpers                                                                    *)
(******************************************************************************)

(** We don't make any effort (yet) to keep track of positions even though Wasm
 * really wants us to. *)
let dummy_phrase what =
  W.Source.(what @@ no_region)

(** A bunch of helpers *)
let mk_var x = dummy_phrase (Int32.of_int x)

let mk_type = function
  | I32 ->
      W.Types.I32Type
  | I64 ->
      W.Types.I64Type

let mk_value s x =
  match s with
  | I32 ->
      W.Values.I32 x
  | I64 ->
      W.Values.I64 x

let mk_int32 i =
  dummy_phrase (W.Values.I32 i)

let mk_int64 i =
  dummy_phrase (W.Values.I64 i)

let mk_const c =
  [ dummy_phrase (W.Ast.Const c) ]

let mk_lit w lit =
  match w with
  | K.Int64 | K.UInt64 ->
      let n = Z.of_string lit in
      let n = if Z.( n >= ~$2 ** 63 ) then Z.( n - ~$2 ** 64 ) else n in
      mk_int64 (Z.to_int64 n)
  | K.Int32 | K.UInt8 | K.UInt16 | K.UInt32 | K.Bool | K.CInt ->
      let n = Z.of_string lit in
      let n = if Z.( n >= ~$2 ** 31 ) then Z.( n - ~$2 ** 32 ) else n in
      mk_int32 (Z.to_int32 n)
  | _ ->
      failwith (KPrint.bsprintf "mk_lit: %s@%s" (K.show_width w) lit)

let i32_mul =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.Mul)) ]

let i32_add =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.Add)) ]

let i32_and =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.And)) ]

let i32_sub =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.Sub)) ]

let i32_xor =
  [ dummy_phrase (W.Ast.Binary (mk_value I32 W.Ast.IntOp.Xor)) ]

let i32_not =
  mk_const (mk_int32 Int32.zero) @
  [ dummy_phrase (W.Ast.Compare (mk_value I32 W.Ast.IntOp.Eq)) ]

let i32_zero =
  mk_const (mk_int32 Int32.zero)

let i32_one =
  mk_const (mk_int32 Int32.one)

let mk_unit =
  i32_zero

let i64_sub =
  [ dummy_phrase (W.Ast.Binary (mk_value I64 W.Ast.IntOp.Sub)) ]

let i64_xor =
  [ dummy_phrase (W.Ast.Binary (mk_value I64 W.Ast.IntOp.Xor)) ]

let i64_not =
  mk_const (mk_int64 Int64.zero) @
  [ dummy_phrase (W.Ast.Compare (mk_value I64 W.Ast.IntOp.Eq)) ]

let mk_drop =
  [ dummy_phrase W.Ast.Drop ]

(* Wasm lacks two crucial instructions: dup (to duplicate the operand at the
 * top of the stack) and swap (to swap the two topmost operands). There are some
 * macros, such as grow_highwater (or 16/8-bit arithmetic), that we want to
 * expand at the last minute (since they use some very low-level Wasm concepts).
 * Therefore, as a convention, every function frame has four "scratch" locals;
 * the first two of size I64; the last two of size I32. The Wasm register
 * allocator will take care of optimizing all of that. *)
let dup32 env =
  [ dummy_phrase (W.Ast.TeeLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 2))) ]

let dup64 env =
  [ dummy_phrase (W.Ast.TeeLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 0))) ]

let swap32 env =
  [ dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 3)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 3))) ]

let swap64 env =
  [ dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 1)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 1))) ]

(* I64 at the top of the stack *)
let swap6432 env =
  [ dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 2))) ]

(* I32 at the top of the stack *)
let swap3264 env =
  [ dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.SetLocal (mk_var (env.n_args + 0)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 2)));
    dummy_phrase (W.Ast.GetLocal (mk_var (env.n_args + 0))) ]


(******************************************************************************)
(* Run-time memory management                                                 *)
(******************************************************************************)

(* We use a bump-pointer allocator called the "highwater mark". One can read it
 * (grows the stack by one); grow it by the specified offset (shrinks the stack
 * by one); restore a value into it (also shrinks the stack by one). *)

(* The highwater mark denotes the top of the stack (bump-pointer allocation).
 * Since it needs to be shared across modules, and since Wasm does not support
 * exported, mutable globals, we use the first word of the (shared) memory for
 * that purpose. *)
let read_highwater =
  i32_zero @
  [ dummy_phrase W.Ast.(Load { ty = mk_type I32; align = 0; offset = 0l; sz = None }) ]

let write_highwater env =
  i32_zero @
  swap32 env @
  [ dummy_phrase W.Ast.(Store { ty = mk_type I32; align = 0; offset = 0l; sz = None }) ]

let grow_highwater env =
  read_highwater @
  i32_add @
  [ dummy_phrase (W.Ast.Call (mk_var (find_func env "WasmSupport_align_64"))) ] @
  write_highwater env


(******************************************************************************)
(* Static memory management (the data segment)                                *)
(******************************************************************************)

(* We want to store constant string literals in the data segment, for efficiency
 * reasons. Since all of our modules share the same linear memory, we proceed as
 * follows. Each module imports, in addition to Kremlin.mem, a constant known as
 * Kremlin.data_start. This module then lays out its strings in the data
 * segment, relative to data_start. Once all strings have been laid out, the
 * module exports its new data_size, and the loader grows Kremlin.data_start by
 * this module's data_size before loading the next module. *)
let compute_string_offset env rel_addr =
  [ dummy_phrase (W.Ast.GetGlobal (mk_var (find_global env "data_start"))) ] @
  [ dummy_phrase (W.Ast.Const (mk_int32 (Int32.of_int rel_addr))) ] @
  i32_add

let mk_string env s =
  let rel_addr =
    try Hashtbl.find env.strings s
    with Not_found ->
      (* Data segment computation will insert the final \000 byte. *)
      let l = String.length s + 1 in
      let rel_addr = !(env.data_size) in
      Hashtbl.add env.strings s rel_addr;
      env.data_size := rel_addr + l;
      rel_addr
  in
  compute_string_offset env rel_addr


(******************************************************************************)
(* Arithmetic                                                                 *)
(******************************************************************************)

let todo w =
  match w with
  | K.Int8 | K.Int16 -> failwith "todo"
  | _ -> ()

(** Binary operations take a width and an operation, in order to pick the right
 * flavor of signed vs. unsigned operation *)
let mk_binop (w, o) =
  let open W.Ast.IntOp in
  match o with
  | K.Add | K.AddW ->
      Some Add
  | K.Sub | K.SubW ->
      Some Sub
  | K.Div | K.DivW ->
      todo w;
      (* Fortunately, it looks like FStar.Int*, C and Wasm all adopt the
       * "rounding towards zero" behavior. Phew! *)
      if K.is_signed w then
        Some DivS
      else
        Some DivU
  | K.Mult | K.MultW ->
      Some Mul
  | K.Mod ->
      todo w;
      if K.is_signed w then
        Some RemS
      else
        Some RemU
  | K.BOr | K.Or ->
      Some Or
  | K.BAnd | K.And ->
      Some And
  | K.BXor | K.Xor ->
      Some Xor
  | K.BShiftL ->
      Some Shl
  | K.BShiftR ->
      todo w;
      if K.is_signed w then
        Some ShrS
      else
        Some ShrU
  | _ ->
      None

let is_binop (o: K.width * K.op) =
  mk_binop o <> None

let mk_cmpop (w, o) =
  let open W.Ast.IntOp in
  match o with
  | K.Eq ->
      Some Eq
  | K.Neq ->
      Some Ne
  | K.BNot | K.Not ->
      failwith "todo not (zero minus?)"
  | K.Lt ->
      todo w;
      if K.is_signed w then
        Some LtS
      else
        Some LtU
  | K.Lte ->
      todo w;
      if K.is_signed w then
        Some LeS
      else
        Some LeU
  | K.Gt ->
      todo w;
      if K.is_signed w then
        Some GtS
      else
        Some GtU
  | K.Gte ->
      todo w;
      if K.is_signed w then
        Some GeS
      else
        Some GeU
  | _ ->
      None

let is_cmpop (o: K.width * K.op) =
  mk_cmpop o <> None

(** Dealing with size mismatches *)

(** The delicate question is how to handle integer types < 32 bits. Two options
 * for signed integers:
 * - keep the most significant bit as the sign bit (i.e; the 32nd bit), and use
 *   the remaining lowest n-1 bits; this means that operations that need to care
 *   about the sign (shift-right, division, remainder) can be builtin Wasm
 *   operations; then, assuming we want to replicate the C semantics:
 *   - signed to larger signed = no-op
 *   - signed to smaller signed = mask & shift sign bit
 *   - unsigned to smaller unsigned = mask
 *   - unsigned to larger unsigned = no-op
 *   - signed to smaller unsigned = mask
 *   - signed to equal or greater unsigned = shift sign bit
 *   - unsigned to smaller or equal signed = mask & shift sign bit
 *   - unsigned to larger signed = no-op
 * - use the lowest n bits and re-implement "by hand" operations that require us
 *   to care about the sign
 *   - signed to larger signed = sign-extension
 *   - signed to smaller signed = mask
 *   - unsigned to smaller unsigned = mask
 *   - unsigned to larger unsigned = no-op
 *   - signed to smaller unsigned = mask
 *   - signed to greater unsigned = sign-extension
 *   - unsigned to smaller or equal signed = mask
 *   - unsigned to larger signed = no-op
 *)
let mk_mask w =
  let open K in
  match w with
  | UInt32 | Int32 | UInt64 | Int64 | CInt ->
      []
  | UInt16 | Int16 ->
      mk_const (mk_int32 0xffffl) @
      i32_and
  | UInt8 | Int8 ->
      mk_const (mk_int32 0xffl) @
      i32_and
  | _ ->
      []

let mk_cast w_from w_to =
  let open K in
  match w_from, w_to with
  | (UInt8 | UInt16 | UInt32), (Int64 | UInt64) ->
      (* Zero-padding, C semantics. That's 12 cases. *)
      [ dummy_phrase (W.Ast.Convert (W.Values.I64 W.Ast.IntOp.ExtendUI32)) ]
  | Int32, (Int64 | UInt64) ->
      (* Sign-extend, then re-interpret, also C semantics. That's 12 more cases. *)
      [ dummy_phrase (W.Ast.Convert (W.Values.I64 W.Ast.IntOp.ExtendSI32)) ]
  | (Int64 | UInt64), (Int32 | UInt32 | Int16 | UInt16 | Int8 | UInt8) ->
      (* Truncate, still C semantics (famous last words?). That's 24 cases. *)
      [ dummy_phrase (W.Ast.Convert (W.Values.I32 W.Ast.IntOp.WrapI64)) ] @
      mk_mask w_to
  | (Int8 | UInt8), (Int8 | UInt8)
  | (Int16 | UInt16), (Int16 | UInt16)
  | (Int32 | UInt32), (Int32 | UInt32)
  | (Int64 | UInt64), (Int64 | UInt64) ->
      []
  | UInt8, (UInt16 | UInt32)
  | UInt16, UInt32 ->
      []
  | UInt16, UInt8
  | UInt32, (UInt16 | UInt8) ->
      mk_mask w_to
  | Bool, _ | _, Bool ->
      invalid_arg "mk_cast"
  | _ ->
      Warn.fatal_error "todo: conversion from %s to %s"
        (show_width w_from) (show_width w_to)


(******************************************************************************)
(* Debugging                                                                  *)
(******************************************************************************)

module Debug = struct

  (** This module provides a set of helpers to insert debugging within the
   * instruction stream. *)

  (* Debugging conventions. We assume some scratch space at the beginning of the
   * memory; bytes 0..3 are the highwater mark, and bytes 4..127 are scratch space
   * to write a series of either:
   * - 1 followed by the address of a zero-terminated string (most likely sitting
   *     in the data segment), or
   * - 2 followed by a 32-bit integer (little-endian, as enforced by Wasm), or
   * - 3 followed by a 64-bit integer (little-endian, as enforced by Wasm), or
   * - 4 increase nesting of call stack, or
   * - 5 decrease nesting of call stack, or
   * - 0 (end of transmission)
   * This is to be read by the (externally-provided) debug function. This space
   * may evolve to include more information. The debug function is always the
   * function imported first (to easily generate debugging code). *)
  let mark_size = 4

  (* Debugging requires only one import, namely the debug function. We could've
   * done things differently, but since Wasm does not support varargs, it
   * would've been hard to write a generic printing routine otherwise. TODO:
   * this info could be written right after the highwater mark, that way, we
   * wouldn't be limited to 124b of debugging info. *)
  let default_imports = [
    dummy_phrase W.Ast.({
      module_name = name_of_string "Kremlin";
      item_name = name_of_string "debug";
      idesc = dummy_phrase (FuncImport (mk_var 0))
    });
  ]

  let default_types = [
    dummy_phrase (W.Types.FuncType ([], []));
      (** not exposed in WasmSupport.fst, no fstar-compatible type. *)
  ]

  let _ =
    assert (List.length default_imports = List.length default_types)

  let mk env l =

    let char ofs c =
      let c = Char.code c in
      mk_const (mk_int32 (Int32.of_int ofs)) @
      mk_const (mk_int32 (Int32.of_int c)) @
      [ dummy_phrase W.Ast.(Store {
          ty = mk_type I32; align = 0; offset = 0l; sz = Some W.Memory.Mem8 })]
    in

    let rec byte_and_store ofs c t f tl =
      char ofs c @
      f (mk_const (mk_int32 (Int32.of_int (ofs + 1)))) @
      [ dummy_phrase W.Ast.(Store {
          ty = mk_type t; align = 0; offset = 0l; sz = None })] @
      aux (if t = I32 then ofs + 5 else ofs + 9) tl

    and aux ofs l =
      match l with
      | [] ->
          if ofs > 127 then
            failwith "Debug information clobbered past the scratch area";
          char ofs '\x00'
      | `String s :: tl ->
          byte_and_store ofs '\x01' I32 (fun addr ->
            addr @ mk_string env s) tl
      | `Peek32 :: tl ->
          byte_and_store ofs '\x02' I32 (fun addr ->
            dup32 env @ addr @ swap32 env) tl
      | `Local32 i :: tl ->
          byte_and_store ofs '\x02' I32 (fun addr ->
            addr @ [ dummy_phrase (W.Ast.GetLocal (mk_var i)) ]) tl
      | `Peek64 :: tl ->
          byte_and_store ofs '\x03' I64 (fun addr ->
            dup64 env @ addr @ swap3264 env) tl
      | `Local64 i :: tl ->
          byte_and_store ofs '\x03' I64 (fun addr ->
            addr @ [ dummy_phrase (W.Ast.GetLocal (mk_var i)) ]) tl
      | `Incr :: tl ->
          char ofs '\x04' @
          aux (ofs + 1) tl
      | `Decr :: tl ->
          char ofs '\x05' @
          aux (ofs + 1) tl
    in
    if Options.debug "wasm-calls" then
      aux mark_size l @
      [ dummy_phrase (W.Ast.Call (mk_var (find_func env "debug"))) ]
    else
      []
end


(******************************************************************************)
(* Initial imports for all modules                                            *)
(******************************************************************************)

module Base = struct
  (* Reminder: the JS loader, as it folds over the list of modules, provides
   * each module with the start address of its own data segment. *)
  let data_start =
    dummy_phrase W.Ast.({
      module_name = name_of_string "Kremlin";
      item_name = name_of_string "data_start";
      idesc = dummy_phrase (GlobalImport W.Types.(
        GlobalType (mk_type I32, Immutable)))})

  let memory =
    let mtype = W.Types.MemoryType W.Types.({ min = 16l; max = None }) in
    dummy_phrase W.Ast.({
      module_name = name_of_string "Kremlin";
      item_name = name_of_string "mem";
      idesc = dummy_phrase (MemoryImport mtype)})

  (* This establishes the func index / type index invariant. *)
  let imports = memory :: data_start :: Debug.default_imports
  let types = Debug.default_types
end


(******************************************************************************)
(* Actual translation from Cflat to Wasm                                      *)
(******************************************************************************)

let mk_binop_conversion (w, o) =
  let open K in
  match w, o with
  | (UInt64 | Int64), (BShiftL | BShiftR) ->
      mk_cast UInt32 UInt64
  | _ ->
      []

let rec mk_callop2 env (w, o) e1 e2 =
  (* TODO: check special byte semantics C / WASM *)
  let size = size_of_width w in
  mk_expr env e1 @
  mk_expr env e2 @
  if is_binop (w, o) then
    mk_binop_conversion (w, o) @
    [ dummy_phrase (W.Ast.Binary (mk_value size (Option.must (mk_binop (w, o))))) ] @
    mk_mask w
  else if is_cmpop (w, o) then
    [ dummy_phrase (W.Ast.Compare (mk_value size (Option.must (mk_cmpop (w, o))))) ] @
    mk_mask w
  else
    failwith "todo mk_callop2"

and mk_callop env (w, o) e1 =
  let open K in
  match (w, o) with
  | (UInt64 | Int64), Not ->
      (* Unused? *)
      mk_expr env e1 @
      i64_not
  | (UInt64 | Int64), BNot ->
      mk_const (mk_int64 Int64.minus_one) @
      mk_expr env e1 @
      i64_xor
  | _, Not ->
      mk_expr env e1 @
      i32_not
  | _, BNot ->
      mk_const (mk_int32 Int32.minus_one) @
      mk_expr env e1 @
      i32_xor
  | _ ->
      failwith ("todo mk_callop " ^ show_width w ^ " " ^ show_op o)

and mk_size size =
  [ dummy_phrase (W.Ast.Const (mk_int32 (Int32.of_int (bytes_in size)))) ]

and mk_expr env (e: expr): W.Ast.instr list =
  match e with
  | Var i ->
      [ dummy_phrase (W.Ast.GetLocal (mk_var i)) ]

  | Constant (w, lit) ->
      mk_const (mk_lit w lit)

  | CallOp (o, [ e1 ]) ->
      mk_callop env o e1

  | CallOp (o, [ e1; e2 ]) ->
      mk_callop2 env o e1 e2

  | CallFunc ("LowStar_Monotonic_Buffer_mnull", [ _ ] )
  | CallFunc ("LowStar_Buffer_null", [ _ ] )
  | CallFunc ("C_Nullity_null", [ _ ]) ->
      [ dummy_phrase (W.Ast.Const (mk_int32 0l)) ]

  (* If the function is a fallback implementation of an intrinsic, call it
   * using its correct name *)
  | CallFunc ("Lib_IntTypes_Intrinsics_add_carry_u64", args) ->
      mk_expr env (CallFunc ("Hacl_IntTypes_Intrinsics_add_carry_u64", args))
  | CallFunc ("Lib_IntTypes_Intrinsics_sub_borrow_u64", args) ->
      mk_expr env (CallFunc ("Hacl_IntTypes_Intrinsics_sub_borrow_u64", args))

  | CallFunc (("load16_le_i" | "load16_le"), [ e ]) ->
      mk_expr env e @
      [ dummy_phrase W.Ast.(Load { ty = mk_type I32; align = 0; offset = 0l; sz = Some W.Memory.(Mem16, ZX) })]

  | CallFunc (("load16_be_i" | "load16_be"), [ e ]) ->
      mk_expr env (CallFunc ("WasmSupport_betole16", [ CallFunc ("load16_le", [ e ])]))

  | CallFunc (("load32_le_i" | "load32_le"), [ e ]) ->
      mk_expr env e @
      [ dummy_phrase W.Ast.(Load { ty = mk_type I32; align = 0; offset = 0l; sz = None })]

  | CallFunc (("load32_be_i" | "load32_be"), [ e ]) ->
      mk_expr env (CallFunc ("WasmSupport_betole32", [ CallFunc ("load32_le", [ e ])]))

  | CallFunc (("load64_le_i" | "load64_le"), [ e ]) ->
      mk_expr env e @
      [ dummy_phrase W.Ast.(Load { ty = mk_type I64; align = 0; offset = 0l; sz = None })]

  | CallFunc (("load64_be_i" | "load64_be"), [ e ]) ->
      mk_expr env (CallFunc ("WasmSupport_betole64", [ CallFunc ("load64_le", [ e ])]))

  | CallFunc (("store128_be_i" | "store128_be"), [ dst; src ])
  | CallFunc (("load128_be_i" | "load128_be"), [ src; dst ]) ->
      let local_src = env.n_args + 2 in
      let local_dst = local_src + 1 in
      (* Using the two 32-bit scratch locals for the two addresses. *)
      mk_expr env src @
      [ dummy_phrase (W.Ast.SetLocal (mk_var local_src)) ] @
      mk_expr env dst @
      [ dummy_phrase (W.Ast.SetLocal (mk_var local_dst)) ] @
      (* Push dst and src on the stack; load src; store. This is low. *)
      [ dummy_phrase (W.Ast.GetLocal (mk_var local_dst)) ] @
      [ dummy_phrase (W.Ast.Const (mk_int32 8l)) ] @
      i32_add @
      [ dummy_phrase (W.Ast.GetLocal (mk_var local_src)) ] @
      [ dummy_phrase W.Ast.(Load { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      [ dummy_phrase (W.Ast.Call (mk_var (find_func env "WasmSupport_betole64"))) ] @
      [ dummy_phrase W.Ast.(Store { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      (* Same thing with +8b offset. This is high. *)
      [ dummy_phrase (W.Ast.GetLocal (mk_var local_dst)) ] @
      [ dummy_phrase (W.Ast.GetLocal (mk_var local_src)) ] @
      [ dummy_phrase (W.Ast.Const (mk_int32 8l)) ] @
      i32_add @
      [ dummy_phrase W.Ast.(Load { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      [ dummy_phrase (W.Ast.Call (mk_var (find_func env "WasmSupport_betole64"))) ] @
      [ dummy_phrase W.Ast.(Store { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      (* This is just a glorified memcpy. *)
      mk_unit

  | CallFunc (("store128_le_i" | "store128_le"), [ dst; src ])
  | CallFunc (("load128_le_i" | "load128_le"), [ src; dst ]) ->
      let local_src = env.n_args + 2 in
      let local_dst = local_src + 1 in
      (* Using the two 32-bit scratch locals for the two addresses. *)
      mk_expr env src @
      [ dummy_phrase (W.Ast.SetLocal (mk_var local_src)) ] @
      mk_expr env dst @
      [ dummy_phrase (W.Ast.SetLocal (mk_var local_dst)) ] @
      (* Push dst and src on the stack; load src; store. This is low. *)
      [ dummy_phrase (W.Ast.GetLocal (mk_var local_dst)) ] @
      [ dummy_phrase (W.Ast.GetLocal (mk_var local_src)) ] @
      [ dummy_phrase W.Ast.(Load { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      [ dummy_phrase W.Ast.(Store { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      (* Same thing with +8b offset. This is high. *)
      [ dummy_phrase (W.Ast.GetLocal (mk_var local_dst)) ] @
      [ dummy_phrase (W.Ast.Const (mk_int32 8l)) ] @
      i32_add @
      [ dummy_phrase (W.Ast.GetLocal (mk_var local_src)) ] @
      [ dummy_phrase (W.Ast.Const (mk_int32 8l)) ] @
      i32_add @
      [ dummy_phrase W.Ast.(Load { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      [ dummy_phrase W.Ast.(Store { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      (* This is just a glorified memcpy. *)
      mk_unit

  | CallFunc (("store16_le_i" | "store16_le"), [ e1; e2 ]) ->
      mk_expr env e1 @
      mk_expr env e2 @
      [ dummy_phrase W.Ast.(Store { ty = mk_type I32; align = 0; offset = 0l; sz = Some W.Memory.Mem16 })] @
      mk_unit

  | CallFunc (("store16_be_i" | "store16_be"), [ e1; e2 ]) ->
      mk_expr env (CallFunc ("store16_le", [ e1; CallFunc ("WasmSupport_betole16", [ e2 ])]))

  | CallFunc (("store32_le_i" | "store32_le"), [ e1; e2 ]) ->
      mk_expr env e1 @
      mk_expr env e2 @
      [ dummy_phrase W.Ast.(Store { ty = mk_type I32; align = 0; offset = 0l; sz = None })] @
      mk_unit

  | CallFunc (("store32_be_i" | "store32_be"), [ e1; e2 ]) ->
      mk_expr env (CallFunc ("store32_le", [ e1; CallFunc ("WasmSupport_betole32", [ e2 ])]))

  | CallFunc (("store64_le_i" | "store64_le"), [ e1; e2 ]) ->
      mk_expr env e1 @
      mk_expr env e2 @
      [ dummy_phrase W.Ast.(Store { ty = mk_type I64; align = 0; offset = 0l; sz = None })] @
      mk_unit

  | CallFunc (("store64_be_i" | "store64_be"), [ e1; e2 ]) ->
      mk_expr env (CallFunc ("store64_le", [ e1; CallFunc ("WasmSupport_betole64", [ e2 ])]))

  | CallFunc (name, es) ->
      KList.map_flatten (mk_expr env) es @
      [ dummy_phrase (W.Ast.Call (mk_var (find_func env name))) ]

  | BufCreate (Common.Stack, n_elts, elt_size) ->
      (* TODO -- generate the equivalent of KRML_CHECK_SIZE *)
      read_highwater @
      mk_expr env n_elts @
      mk_size elt_size @
      i32_mul @
      grow_highwater env

  | BufRead (e1, ofs, size) ->
      (* github.com/WebAssembly/spec/blob/master/interpreter/spec/eval.ml#L189 *)
      mk_expr env e1 @
      [ dummy_phrase W.Ast.(Load {
        (* the type we want on the operand stack *)
        ty = mk_type (if size = A64 then I64 else I32);
        (* ignored *)
        align = 0;
        (* in number of bytes *)
        offset = Int32.of_int ofs;
        (* we store 32-bit integers in 32-bit slots, and smaller than that in
         * 32-bit slots as well, so no conversion M32 for us *)
        sz = match size with
          | A16 -> Some W.Memory.(Mem16, ZX)
          | A8 -> Some W.Memory.(Mem8, ZX)
          | _ -> None })]

  | BufSub (e1, e2, size) ->
      mk_expr env e1 @
      mk_expr env e2 @
      mk_size size @
      i32_mul @
      i32_add

  | Cast (e1, w_from, w_to) ->
      mk_expr env e1 @
      mk_cast w_from w_to

  | IfThenElse (e, b1, b2, s) ->
      let s = mk_type s in
      mk_expr env e @
      [ dummy_phrase (W.Ast.If ([ s ], mk_expr env b1, mk_expr env b2)) ]

  | Assign (i, e) ->
      mk_expr env e @
      [ dummy_phrase (W.Ast.SetLocal (mk_var i)) ] @
      mk_unit

  | BufWrite (e1, ofs, e3, size) ->
      mk_expr env e1 @
      mk_expr env e3 @
      [ dummy_phrase W.Ast.(Store {
        ty = mk_type (if size = A64 then I64 else I32);
        align = 0;
        offset = Int32.of_int ofs;
        sz = match size with
          | A16 -> Some W.Memory.Mem16
          | A8 -> Some W.Memory.Mem8
          | _ -> None })] @
      mk_unit

  | While (e, expr) ->
      [ dummy_phrase (W.Ast.Loop ([],
        mk_expr env e @
        [ dummy_phrase (W.Ast.If ([],
          read_highwater @
          mk_expr env expr @
          mk_drop @
          write_highwater env @
          [ dummy_phrase (W.Ast.Br (mk_var 1)) ],
          [ dummy_phrase W.Ast.Nop ])) ]
      ))] @
      mk_unit

  | Ignore (e, _) ->
      mk_expr env e @
      mk_drop @
      mk_unit

  | Sequence es ->
      if List.length es = 0 then
        mk_unit
      else
        let es, e = KList.split_at_last es in
        List.flatten (List.map (fun e ->
          mk_expr env e @
          [ dummy_phrase W.Ast.Drop ]
        ) es) @
        mk_expr env e


  | GetGlobal i ->
      [ dummy_phrase (W.Ast.GetGlobal (mk_var (find_global env i))) ]

  | StringLiteral s ->
      (* These strings are '\0'-terminated... revisit? *)
      mk_string env s

  | Abort s ->
      (* Must use unreachable to have a polymorphic return type (aborts might
       * stem from something in an expression return position). Alternatively,
       * consider keeping the type (or size) that is expected. *)
      mk_expr env s @
      [ dummy_phrase (W.Ast.Call (mk_var (find_func env "WasmSupport_trap"))) ] @
      [ dummy_phrase W.Ast.Unreachable ]

  | Switch (e, branches, default, s) ->
      let vmax = KList.max (List.map (fun (c, _) -> Z.of_string (snd c)) branches) in
      let vmin = KList.min (List.map (fun (c, _) -> Z.of_string (snd c)) branches) in
      if Z.( gt vmax ~$10 || lt vmin ~$0 ) then
        failwith "TODO: in AstToCFlat, don't pick Switch for matches on integers!";

      (*
      block
        block
          block
            block
              br_table $value (table 0 1 2)
            end
            call do_thing1
            br 2
          end
          call do_thing2
          br 1
        end
        call do_thing3
        br 0
      end
      *)
      let n = List.length branches in
      let table = Array.make (Z.to_int vmax + 2) (mk_var 0) in
      let s = mk_type s in
      let dummy =
        match s with
        | W.Types.I32Type -> mk_const (mk_int32 0l)
        | W.Types.I64Type -> mk_const (mk_int64 0L)
        | _ -> assert false
      in
      let rec mk i branches =
        match branches with
        | ((_, c), body) :: branches ->
            let c = int_of_string c in
            table.(c) <- mk_var (n - i);
            [ dummy_phrase (W.Ast.Block ([ s ],
                mk (i + 1) branches @
                mk_expr env body @
                [ dummy_phrase (W.Ast.Br (mk_var i))]))]
        | [] ->
            let default = match default with
              | Some default -> mk_expr env default
              | None -> [ dummy_phrase W.Ast.Unreachable ]
            in
            assert (i = n);
            (* 0 is a special case which corresponds to both the default jump
             * case, for non-contiguous jump tables, and the out-of-bounds case,
             * which happens if the switch does not cover the last constructors.
             * *)
            [ dummy_phrase (W.Ast.Block ([ s ],
              [ dummy_phrase (W.Ast.Block ([ s ],
                dummy @
                mk_expr env e @
                [ dummy_phrase (W.Ast.BrTable (Array.to_list table, mk_var 0))]))] @
              mk_drop @
              default @
              [ dummy_phrase (W.Ast.Br (mk_var n))]))]
      in
      mk 0 branches

  | _ ->
      failwith ("not implemented; got: " ^ show_expr e)

let mk_func_type' args ret =
  dummy_phrase (W.Types.( FuncType (
    List.map mk_type args,
    List.map mk_type ret)))

let mk_func_type { args; ret; _ } =
  mk_func_type' args ret

let mk_func env { args; locals; body; name; ret; _ } =
  let i = find_func env name in
  let env = { env with n_args = List.length args } in

  let body =
    (* Mostly a bunch of debugging info. *)
    let debug_enter = `String name :: `Incr ::
      List.mapi (fun i arg ->
        match arg with
        | I32 ->
            `Local32 i
        | I64 ->
            `Local64 i
      ) args
    in
    let debug_exit = [ `String "return"; `Decr ] @
      match ret with
      | [ I32 ] -> [ `Peek32 ]
      | [ I64 ] -> [ `Peek64 ]
      | _ -> []
    in
    (if name <> "WasmSupport_align_64" then Debug.mk env debug_enter else []) @
    read_highwater @
    mk_expr env body @
    (match ret with
      | [ I32 ] -> swap32 env
      | [ I64 ] -> swap6432 env
      | _ -> []) @
    write_highwater env @
    if name <> "WasmSupport_align_64" then Debug.mk env debug_exit else []
  in

  let locals = List.map mk_type locals in
  let ftype = mk_var i in
  dummy_phrase W.Ast.({ locals; ftype; body })

let mut_of_bool = function
  | true -> W.Types.Mutable
  | false -> W.Types.Immutable

(* Some globals, such as string constants, generate non-constant expressions for
 * their bodies; we provide a dummy and remember to run the initializer at
 * module load-time.
 *
 * For complex globals that contain deep references to other globals, post_init
 * is non-empty and contains a sequence of instructions to initialize such
 * fields. *)
let mk_global env name size body post_init =
  let body = mk_expr env body in
  if Options.debug "wasm" then
    KPrint.bprintf "Constant %s: length(body)=%d, length(post_init)=%d\n"
      name (List.length body) (List.length post_init);
  let post_init =
    if post_init = [] then
      []
    else
      mk_expr env (CFlat.Sequence post_init) @ mk_drop
  in
  let init, body, mut =
    if List.length body > 1 then
      body @ [ dummy_phrase (W.Ast.SetGlobal (mk_var (find_global env name))) ] @ post_init,
      [ dummy_phrase (W.Ast.Const (match size with I32 -> mk_int32 0l | I64 -> mk_int64 0L))],
      true
    else
      post_init, body, false
  in
  init, dummy_phrase W.Ast.({
    gtype = W.Types.GlobalType (mk_type size, mut_of_bool mut);
    value = dummy_phrase body
  }), mut


(******************************************************************************)
(* Putting it all together: generating a Wasm module                          *)
(******************************************************************************)

(* From [types] (all the function types in the universe) and [imports] (some
 * globals, a memory, and exactly [List.length types] functions who come in the
 * same order as [types]), build a current module; as a bonus, grow [types] and
 * [imports] with the exports from this module. *)
let mk_module types imports (name, decls):
  W.Types.func_type W.Source.phrase list * W.Ast.import list * (string * W.Ast.module_) =

  if Options.debug "wasm" then
    KPrint.bprintf ">>> Numbering import-exports for %s\n" name;

  (* Layout the import and types for the current module. The current module's
   * types start with [types]; the current module's imports starts with
   * [imports]. We fold over these to build our environment's maps, which
   * associate to each function & global an index. The Wasm function
   * (resp. globals) index space is made up of all the imported functions (resp.
   * globals), then the current module's functions (resp. globals). *)
  let rec assign env f g imports =
    (* We have seen [f] functions and [g] globals. *)
    match imports with
    | { W.Source.it = { W.Ast.item_name; idesc = { W.Source.it = W.Ast.FuncImport n; _ }; _ }; _ } :: tl ->
        let env = { env with funcs = StringMap.add (string_of_name item_name) f env.funcs } in
        assert (Int32.to_int n.W.Source.it = f);
        assign env (f + 1) g tl
    | { W.Source.it = { W.Ast.item_name; idesc = { W.Source.it = W.Ast.GlobalImport _; _ }; _ }; _ } :: tl ->
        let env = { env with globals = StringMap.add (string_of_name item_name) g env.globals } in
        assign env f (g + 1) tl
    | _ :: tl ->
        (* Intentionally skipping other imports (e.g. memory). *)
        assign env f g tl
    | [] ->
        f, g, env
  in
  let n_imported_funcs, n_imported_globals, env = assign empty 0 0 imports in

  assert (n_imported_funcs = List.length types);

  (* For every global and function that's assumed (via "assume val"), we
   * generate an import request. This means they are implemented "natively". *)
  let rec assign env imports f g decls =
    match decls with
    | ExternalFunction (fname, _, _) :: tl when not (is_primitive fname) ->
        if Options.debug "wasm" then
          KPrint.bprintf "Imported function $%d is %s\n" f fname;
        let env = { env with funcs = StringMap.add fname f env.funcs } in
        let imports =
          dummy_phrase W.Ast.({
            module_name = name_of_string name;
            item_name = name_of_string fname;
            idesc = dummy_phrase (FuncImport (mk_var f))
          }) :: imports
        in
        assign env imports (f + 1) g tl
    | ExternalGlobal (gname, t) :: tl ->
        let env = { env with globals = StringMap.add gname g env.globals } in
        let imports =
          dummy_phrase W.Ast.({
            module_name = name_of_string name;
            item_name = name_of_string gname;
            idesc = dummy_phrase (
              GlobalImport W.Types.(GlobalType (mk_type t, W.Types.Immutable)))
          }) :: imports
        in
        assign env imports f (g + 1) tl
    | _ :: tl ->
        assign env imports f g tl
    | [] ->
        List.rev imports, f, g, env
  in
  let imports', n_imported_funcs, n_imported_globals, env =
    assign env [] n_imported_funcs n_imported_globals decls
  in
  let imports = imports @ imports' in

  (* Generate types for the assumed function declarations. Re-establish the invariant
   * that the function at index i in the function index space has type i in the
   * types index space. *)
  let types = types @ KList.filter_map (function
    | ExternalFunction (fname, args, ret) when not (is_primitive fname)->
        Some (mk_func_type' args ret)
    | _ ->
        None
  ) decls in

  (* Continue filling our environment with the rest of the function (resp.
   * global) index space, namely, this module's functions (resp. globals) *)
  let rec assign env f g = function
    | Function { name; _ } :: tl ->
        let env = { env with funcs = StringMap.add name f env.funcs } in
        assign env (f + 1) g tl
    | Global (name, _, _, _, _) :: tl ->
        let env = { env with globals = StringMap.add name g env.globals } in
        assign env f (g + 1) tl
    | _ :: tl ->
        (* Intentionally skipping type declarations. *)
        assign env f g tl
    | [] ->
        env
  in
  let env = assign env n_imported_funcs n_imported_globals decls in

  if Options.debug "wasm" then
    debug name env;

  (* START detour to generate the next module's import table. *)

  (* Subtlety: we do not want to export private functions. So, we build a
   * slightly different list of types, to which we only append public types.
   * This means that we can't poke at the environment to find the index of a
   * given function in this list. *)
  let types_only_public = types @ KList.filter_map (function
    | Function f when f.public ->
        Some (mk_func_type f)
    | _ ->
        None
  ) decls in

  (* Now, this means that we can easily extend [imports] with our own functions
   * & globals, to be passed to the next module when they want to import all the
   * stuff in the universe, including the current module's "stuff". Note: this
   * maintains the invariant that the i-th function in [imports_me_included]
   * points to type index i. *)
  let _, my_imports = List.fold_left (fun (next_func, acc) -> function
    | Function f when f.public ->
        if Options.debug "wasm" then
          KPrint.bprintf "Imported function $%d is %s\n" next_func f.name;
        next_func + 1, dummy_phrase W.Ast.({
          module_name = name_of_string name;
          item_name = name_of_string f.name;
          idesc = dummy_phrase (FuncImport (mk_var next_func))
        }) :: acc
    | Global (g_name, size, _, _, public) when public ->
        let t = mk_type size in
        next_func, dummy_phrase W.Ast.({
          module_name = name_of_string name;
          item_name = name_of_string g_name;
          idesc = dummy_phrase (
            GlobalImport W.Types.(GlobalType (t, W.Types.Immutable)))
        }) :: acc
    | _ ->
        next_func, acc
  ) (List.length types, []) decls in
  let imports_me_included = imports @ List.rev my_imports in

  (* END detour to generate the next module's import table. *)

  (* Generate types for the function declarations. Re-establish the invariant
   * that the function at index i in the function index space has type i in the
   * types index space. *)
  let types = types @ KList.filter_map (function
    | Function f ->
        Some (mk_func_type f)
    | _ ->
        None
  ) decls in

  (* Compile the functions. *)
  let funcs = KList.filter_map (function
    | Function f ->
        begin try Some (mk_func (locate env (In f.name)) f) with
        | e ->
            KPrint.bprintf "Failed to compile %s from CFlat to Wasm\n%s\n"
              f.name (Printexc.to_string e);
            Printexc.print_backtrace stderr;
            failwith "wasm function numbering is going to be off, can't proceed"
        end
    | _ ->
        None
  ) decls in

  (* The globals, too. Global have their types directly attached to them and do
   * not rely on an indirection via a type table like functions. *)
  let inits, globals = List.fold_left (fun (inits, globals) d ->
    match d with
    | Global (name, size, body, post, public) ->
        let init, global, mut = mk_global env name size body post in
        if mut && public then
          Warn.fatal_error "Global %s is public and mutable; this is going \
            to be rejected by the WASM validator." name;
        init :: inits, global :: globals
    | _ ->
        inits, globals
  ) ([], []) decls in
  let globals = List.rev globals in

  (* If some globals need to be initialized at module initialization-time, write
   * them out in a function appended at the end of the list which breaks our
   * invariant. *)
  let inits = List.flatten (List.rev inits) in
  let funcs, types, start =
    if List.length inits = 0 then
      funcs,
      types,
      None
    else
      let last_func_index = n_imported_funcs + List.length funcs in
      funcs @ [ dummy_phrase W.Ast.({ locals = []; ftype = mk_var last_func_index; body = inits })],
      types @ [ mk_func_type' [] [] ],
      Some (mk_var last_func_index)
  in

  (* Side-effect: the table is now filled with all the string constants that
   * need to be laid out in the data segment. Compute said data segment.
   * Reminder: the data segment is just a convenient way to initialize memory at
   * module load-time. *)
  let data =
    let size = !(env.data_size) in
    let buf = Bytes.create size in
    if Options.debug "wasm" then
      KPrint.bprintf "Writing out a data segment of size %d\n" size;
    Hashtbl.iter (fun s rel_addr ->
      if Options.debug "wasm" then
        KPrint.bprintf "  0x%4x: %s\n" rel_addr (String.escaped s);
      let l = String.length s in
      String.blit s 0 buf rel_addr l;
      Bytes.set buf (rel_addr + l) '\000';
    ) env.strings;
    [ dummy_phrase W.Ast.({
        index = mk_var 0;
        offset = dummy_phrase [ dummy_phrase (
          W.Ast.GetGlobal (mk_var (find_global env "data_start"))) ];
        init = Bytes.to_string buf })]
  in

  (* We also to export how big is our data segment so that the next module knows
   * where to start laying out its own static data in the globally-shared
   * memory. *)
  let data_size_index = n_imported_globals + List.length globals in
  let globals = globals @ [ dummy_phrase W.Ast.({
    gtype = W.Types.GlobalType (mk_type I32, W.Types.Immutable);
    value = dummy_phrase (mk_const (mk_int32 (Int32.of_int !(env.data_size))))
  })] in

  (* Export all of the current module's functions & globals. *)
  let exports = KList.filter_map (function
    | Function { public; name; _ } when public ->
        Some (dummy_phrase W.Ast.({
          name = name_of_string name;
          edesc = dummy_phrase (W.Ast.FuncExport (mk_var (find_func env name)));
        }))
    | Global (name, _, _, _, public) when public ->
        Some (dummy_phrase W.Ast.({
          name = name_of_string name;
          edesc = dummy_phrase (W.Ast.GlobalExport (mk_var (find_global env name)));
        }))
    | _ ->
        None
  ) decls @ [
    dummy_phrase W.Ast.({
      name = name_of_string "data_size";
      edesc = dummy_phrase (W.Ast.GlobalExport (mk_var data_size_index));
    })]
  in

  let module_ = dummy_phrase W.Ast.({
    empty_module with
    funcs;
    types;
    globals;
    exports;
    imports;
    data;
    start
  }) in
  types_only_public, imports_me_included, (name, module_)


(* Since the modules are already topologically sorted, we make each module
 * import all the exports from all the previous modules. [imports] is a list of
 * everything that been made visible so far... ideally, we should only import
 * things that we need. *)
let mk_files files =
  let _, _, modules = List.fold_left (fun (types, imports, modules) file ->
    let types, imports, module_ = mk_module types imports file in
    types, imports, module_ :: modules
  ) (Base.types, Base.imports, []) files in
  List.rev modules
