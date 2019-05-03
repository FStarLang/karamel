module IfThenElse

open FStar.HyperStack.ST

let test (): St bool =
  true

let main (): St Int32.t =

  let x =
    if test () then
      if test () then
        test ()
      else
        let x = test () in
        x || x
    else
      let x = test () in
      x && x
  in
  if x then 0l else 0l
