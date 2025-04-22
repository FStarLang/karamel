module RustFn

module U32 = FStar.UInt32

let add_one (x: U32.t): U32.t =
  x `FStar.UInt32.add_mod` 1ul

let call (f: U32.t -> U32.t) (x: U32.t): U32.t = f x

noeq type foo = { f: bool -> bool }
let f b = not b
let g () : foo = { f }
let h (x: foo) = x.f true

let main_ () = call add_one 0ul `FStar.UInt32.sub_mod` 1ul
