module AbstractStruct2
open FStar.HyperStack.ST
module B = LowStar.Buffer

[@@CAbstractStruct]
val handle : Type0

val init (_:unit)
  : ST (B.pointer handle)
       (requires fun _ -> True)
       (ensures fun _ handle h1 -> B.live h1 handle)

val main: unit -> St Int32.t
