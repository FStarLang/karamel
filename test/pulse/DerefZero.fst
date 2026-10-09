module DerefZero

module U32 = FStar.UInt32

let zero_for_deref : U32.t = Pulse.Lib.Pervasives._zero_for_deref

let direct () : U32.t = Pulse.Lib.Pervasives._zero_for_deref

let aliased () : U32.t = zero_for_deref

let add (x: U32.t) : U32.t =
  U32.add_mod x Pulse.Lib.Pervasives._zero_for_deref

type pair = { a: U32.t; b: U32.t }

private let zeros : pair = {
  a = Pulse.Lib.Pervasives._zero_for_deref;
  b = 0ul
}

let record_field () : U32.t = zeros.a
