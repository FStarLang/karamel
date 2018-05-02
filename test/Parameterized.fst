module Parameterized

//
open FStar.Int32
open FStar.HyperStack.ST
open TestLib

let lbytes n =
  b:Buffer.buffer UInt8.t { Buffer.length b = n }

let skey _ _ =
  lbytes 8

let akey x y =
  option (skey x y)

let get (k: akey unit unit { Some? k }) =
  match k with
  | Some k -> k

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  pop_frame ();
  C.EXIT_SUCCESS

