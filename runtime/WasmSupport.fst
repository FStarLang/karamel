module WasmSupport

open FStar.HyperStack.ST

module U32 = FStar.UInt32

(* Functions implemented primitively in JS. *)

assume val trap: unit -> Stack unit (fun _ -> True) (fun _ _ _ -> True)

(* Functions that the code-generator expects to find, either at the Ast, CFlat
or Wasm levels. In SimplifyWasm.ml, we prefix these with their module (before
"to_c_names". After that, e.g. in CFlatToWasm.ml, we can refer to them with
their short names, i.e. __. *)

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
