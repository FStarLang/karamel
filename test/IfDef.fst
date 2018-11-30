module IfDef

[@ CIfDef ]
assume val x: bool

let main (): Int32.t =
  if x then
    0l
  else
    1l
