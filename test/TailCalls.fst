module TailCalls

open FStar.HyperStack.ST

module B = FStar.Buffer

let rec main (argc: Int32.t) (argv: B.buffer C.String.t) : St Int32.t =
  if argc = 0l then
    0l
  else
    main (FStar.Int32.(argc -^ 1l)) argv
