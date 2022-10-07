module SteelArray

open Steel.Effect
open Steel.Array

noextract inline_for_extraction
let l = [0uy; 1uy]

let test () : SteelT Int32.t emp (fun _ -> emp) =
  let r = malloca_of_list l in
  let x = index r 0ul in
  if x = 0uy then (
    free r;
    1l
  ) else (
    free r;
    0l
  )
