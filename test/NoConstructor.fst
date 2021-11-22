module NoConstructor

inline_for_extraction
let t = (x: Int32.t & unit)

let f () : Tot t = (| 0l, () |)

let main (): Int32.t =
  dfst (f ())
