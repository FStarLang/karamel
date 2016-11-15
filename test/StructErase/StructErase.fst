module StructErase
open FStar.Int32
open FStar.ST

type u = { left: Int32.t; right: Int32.t }

let rec f (r: u) (n: Int32.t): Stack unit (fun _ -> true) (fun _ _ _ -> true)  =
 push_frame();
 (
  if lt n 1l
  then ()
  else
   let r' : u = { left = sub r.right 1l ; right = add r.left 1l } in
   f r' (sub n 1l)
 );
 pop_frame()

let test () = 
 let r : u = { left = 18l ; right = 42l } in
 let z2 = mul 2l 2l in
 let z4 = mul z2 z2 in
 let z8 = mul z4 z4 in
 let z16 = mul z8 z8 in
 let z24 = mul z8 z16 in
 let z = mul z24 z2 in
 f r z
