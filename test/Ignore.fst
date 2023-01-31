module Ignore

open LowStar.Ignore

let main (argc: Int32.t) (argv: LowStar.Buffer.(buffer (buffer C.char))) =
  ignore argc;
  ignore argv;
  0l
