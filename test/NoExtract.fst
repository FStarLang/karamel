module NoExtract

// THIS KIND OF STUFF IS SUPER DISCOURAGED!!

open FStar.HyperStack.ST

noextract
let f (): St Int32.t = 1l

[@ (CPrologue "int f (void *x) { return 0; }") ]
private
let g () = 1l

let b (): St bool = true

let main () =
  if b () then
    f ()
  else
    g ()
