module Rustfn3
module B = LowStar.Buffer
open FStar.HyperStack.ST

inline_for_extraction
type t = r:B.lbuffer bool 1 -> Stack UInt32.t (requires fun h0 -> B.live h0 r) (ensures fun _ _ _ -> True)

noeq type s = {
  r: bool;
  f: t;
}

let f : t = fun r ->
  B.upd r 0ul true;
  0ul

// TODO: propagate mut from field type to function definition
// let g : t = fun r ->
//   0ul

let h () =
  push_frame ();
  let ptr = B.alloca false 1ul in
  let x = { r = false; f } in
  let ret = x.f ptr in
  // let y = { r = false; f = g } in
  // let ret = UInt32.add ret (y.f ptr) in
  pop_frame ();
  ret

let main_ () =
  h ()