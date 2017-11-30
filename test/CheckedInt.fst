module CheckedInt

open FStar.HyperStack.ST

let one (): Stack int (fun _ -> true) (fun _ _ _ -> true) =
  1
let two (): Stack int (fun _ -> true) (fun _ _ _ -> true) =
  2

let main (): Stack int (fun _ -> true) (fun _ _ _ -> true) =
  one () + one () - two ()
