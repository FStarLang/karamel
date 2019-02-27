module IfDef

[@ CIfDef ]
assume val x: bool

[@ CIfDef ]
assume val y: bool

let main (): Int32.t =
  if x && y then
    1l
  else if x || y then
    0l
  else
    1l
