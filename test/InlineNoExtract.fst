module InlineNoExtract

open FStar.HyperStack.ST

noextract
inline_for_extraction
let f (): St Int32.t = 0l

private
let g () = 1l

let b (): St bool = true

let main () =
  if b () then
    f ()
  else
    g ()
