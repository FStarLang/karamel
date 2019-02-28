module IfDef

open FStar.HyperStack.ST

[@ CIfDef ]
assume val x: bool

[@ CIfDef ]
assume val y: bool

let foo (): FStar.HyperStack.ST.Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let test b: FStar.HyperStack.ST.Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  if x then
    if b then
      foo ()
    else
      ()

let bar (): FStar.HyperStack.ST.Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

let test2 () =
  if bar () then
    0ul
  else if bar () then
    1ul
  else if bar () then
    2ul
  else
    3ul


let main (): Int32.t =
  if x && y then
    1l
  else if x || y then
    0l
  else
    1l
