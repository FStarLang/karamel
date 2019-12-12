module Macro

open FStar.Integers

[@ CMacro ]
private
let xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx = 2l + 3l - 5l

[@ CMacro ]
let y = false

[@ CIfDef ]
assume val test: bool

let main () =
  if test then
    -1l
  else
    xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx

