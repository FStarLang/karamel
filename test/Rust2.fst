module Rust2

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

let fully_static (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca 0ul 6ul in
  let x0 = B.sub x 0ul 2ul in
  let x1 = B.sub x 2ul 2ul in
  B.upd x0 0ul 1ul;
  B.upd x1 0ul 1ul;
  B.upd x 0ul 1ul;
  pop_frame ()

let main (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  fully_static ()
