module ArrayReborrowData

module B = LowStar.Buffer

type foo = { a: Int32.t; b: Int32.t }

// This test deliberately allocates a global array.
#push-options "--warn_error -272"
let table = B.gcmalloc_of_list FStar.HyperStack.root
  [ { a = 1l; b = 2l }; { a = 3l; b = 4l } ]
#pop-options
