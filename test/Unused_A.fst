module Unused_A

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

let callee (x: U32.t) (b: B.buffer U32.t) : HST.St bool =
  x `U32.gt` 4ul

let callee_gets_eliminated (foobar: U32.t) (b: B.buffer U32.t) : HST.St bool =
  callee foobar b

let caller (x: U32.t) (b: B.buffer U32.t) : HST.St bool =
  callee_gets_eliminated x b
