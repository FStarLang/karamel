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
