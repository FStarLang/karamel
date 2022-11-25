module IfDefKrml
open FStar.HyperStack.ST
open LowStar.Buffer
[@@CIfDef]
assume
val flag : bool


let something_effectful (x:bool) : Stack bool (requires λ _ → ⊤) (ensures (λ _ _ _ → ⊤)) = x

let test (x y:bool) =
  let z =
    if flag
    then false
    else let aa = something_effectful x in
         aa
  in
  let z =
    if flag
    then false
    else let aa = something_effectful z in
         aa
  in z

let main () = if test true true then 0l else 1l
