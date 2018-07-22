module AbstractStruct

open FStar.HyperStack.ST

[@CAbstractStruct]
type t = {
  x: Int32.t;
}

let main (): St Int32.t =
  let x: t = { x = 0l } in
  x.x
