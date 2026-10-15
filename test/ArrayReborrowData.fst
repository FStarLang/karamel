module ArrayReborrowData

module B = LowStar.Buffer

type foo = { a: Int32.t; b: Int32.t }

let table = B.gcmalloc_of_list FStar.HyperStack.root
  [ { a = 1l; b = 2l }; { a = 3l; b = 4l } ]
