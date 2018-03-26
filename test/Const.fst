module Const

module B = FStar.Buffer

[@ (CConst "argv") ]
let main (argc: FStar.Int32.t) (argv: B.buffer (B.buffer C.char)) =
  0l
