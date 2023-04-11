module WasmSupport

open FStar.HyperStack.ST

module C = FStar.Int.Cast
module I64 = FStar.Int64
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module B = LowStar.Buffer

open LowStar.BufferOps
open FStar.Mul

(* Functions implemented primitively in JS. No F* client should call those! *)

assume val trap: Prims.string -> Stack unit (fun _ -> True) (fun _ _ _ -> False)

(* Really not meant to be called by F* clients... *)
assume val malloc: U32.t -> Stack U32.t (fun _ -> False) (fun _ _ _ -> False)

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
    trap "Zero-sized arrays are not supported in C and in WASM either. See WasmSupport.fst"

let betole16 (x: FStar.UInt16.t) =
  let open FStar.UInt16 in
  logor
    (logand (shift_right x 8ul) 0x00FFus)
    (logand (shift_left x 8ul) 0xFF00us)

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

let memzero (x: B.buffer UInt8.t) (len: UInt32.t) (sz: UInt32.t): Stack unit
  (requires fun h0 -> B.live h0 x /\ sz <> 0ul /\ B.length x = U32.v len * U32.v sz)
  (ensures (fun h0 _ h1 -> B.(modifies (loc_buffer x) h0 h1)))
=
  if len `U32.gte` (0xfffffffful `U32.div` sz) then
    trap "Overflow in memzero; see WasmSupport.fst";
  let n_bytes = U32.mul len sz in
  let h0 = FStar.HyperStack.ST.get () in
  C.Loops.for 0ul n_bytes (fun h _ ->
    B.live h x /\
    B.(modifies (loc_buffer x) h0 h)
  ) (fun i ->
    x.(i) <- 0uy
  )
