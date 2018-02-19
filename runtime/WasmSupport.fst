module WasmSupport

open FStar.HyperStack.ST

module C = FStar.Int.Cast
module I64 = FStar.Int64
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(* Functions implemented primitively in JS. *)

assume val trap: unit -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

(* Functions that the code-generator expects to find, either at the Ast, CFlat
 * or Wasm levels. In SimplifyWasm.ml, we prefix these with their module (before
 * "to_c_names". After that, e.g. in CFlatToWasm.ml, we can refer to them with
 * their short names, e.g. align_64. *)

(* Round up to the nearest multiple of 64. *)
let align_64 (x: U32.t): Tot U32.t =
  if not ( U32.((x &^ 0x07ul) =^ 0ul) ) then
    U32.( (x &^ lognot 0x07ul) +%^ 0x08ul )
  else
    x

(* Non-zero sizes are not supported, period. *)
let check_buffer_size (s: U32.t): Stack unit (fun _-> True) (fun _ _ _ -> True) =
  if U32.( s =^ 0ul ) then
    trap ()

(* TODO: all of these functions are copy-pastes from whatever is written in
 * kremlib.h. They OUGHT TO BE implement in F*! *)
let eq_mask64 (x y: U64.t) =
  let open FStar.UInt64 in
  let x = lognot (logxor x y) in
  let x = shift_left x 32ul in
  let x = shift_left x 16ul in
  let x = shift_left x 8ul in
  let x = shift_left x 4ul in
  let x = shift_left x 2ul in
  let x = shift_left x 1ul in
  FStar.Int64.( shift_right (FStar.Int.Cast.uint64_to_int64 x) 63ul )

let gte_mask64 (x y: U64.t) =
  let low63 = U64.lognot (C.int64_to_uint64 (I64.shift_right
    (I64.sub
      (C.uint64_to_int64 (U64.logand x 0x7fffffffffffffffUL))
      (C.uint64_to_int64 (U64.logand y 0x7fffffffffffffffUL)))
    63ul))
  in
  let high_bit = U64.lognot (C.int64_to_uint64 (I64.shift_right
    (I64.sub
      (C.uint64_to_int64 (U64.logand x 0x8000000000000000UL))
      (C.uint64_to_int64 (U64.logand y 0x8000000000000000UL)))
    63ul))
  in
  U64.logand low63 high_bit

let betole32 (x: U32.t) =
  let open U32 in
  logor (logor (logor (logand (shift_right x 24ul) 0x000000FFul)
    (logand (shift_right x 8ul) 0x0000FF00ul))
    (logand (shift_left x 8ul) 0x00FF0000ul))
    (logand (shift_left x 24ul) 0xFF000000ul)

let betole64 (x: U64.t) =
  let low = C.uint32_to_uint64 (betole32 (C.uint64_to_uint32 x)) in
  let high = C.uint32_to_uint64 (betole32 (C.uint64_to_uint32 (U64.shift_right x 32ul))) in
  U64.logor (U64.shift_left low 32ul) high
