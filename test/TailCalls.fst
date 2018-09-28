module TailCalls

let rec main (argc: Int32.t) (argv: LowStar.Buffer.buffer C.String.t):
  FStar.HyperStack.ST.St int
=
  List.length (List.rev [ 1 ]) - 1
