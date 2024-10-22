module KrmlTrue

let some_effectul_function (x:unit) : Dv unit = ()

let test (x:unit)
: Dv unit
= let res =
    let _ = some_effectul_function x in
    true
  in
  some_effectul_function x

let main () =
  test ();
  0l
