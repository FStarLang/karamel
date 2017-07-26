module WasmSupport

module U32 = FStar.UInt32

(* A set of functions that the code-generator expects to find. *)
let align_64 (x: U32.t): U32.t =
  if not ( U32.((x &^ 0x07ul) =^ 0ul) ) then
    U32.( x &^ 0x07ul +%^ 0x08ul )
  else
    x
