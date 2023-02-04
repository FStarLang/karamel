module AbstractStructAbstract

type t a = (bool & a)

let make #a x = (false, x)
let read #a t = snd t
