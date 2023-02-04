module SteelNotNull

open Steel.Effect
open Steel.Reference

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let r = malloc 0ul in
  if is_null r then (
    free r;
    1l
  ) else (
    free r;
    0l
  )
