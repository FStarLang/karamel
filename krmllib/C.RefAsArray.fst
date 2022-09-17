module C.RefAsArray

// An index to be used as argument to Buffer.index so that
// b[_zero_for_deref] is turned into *b
// Special treatment: marked to not be emitted to C
// in CStarToC11.builtin_names
let _zero_for_deref : FStar.UInt32.t = 0ul
