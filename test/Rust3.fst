module Rust3

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

let root_alias (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca 0UL 6ul in
  let x0 = B.sub x 0ul 2ul in
  let x1 = B.sub x 2ul 2ul in

  let x00 = B.sub x0 0ul 1ul in
  let x01 = B.sub x0 1ul 1ul in

  B.upd x00 0ul 2UL;
  B.upd x0 0ul 2UL;
  B.upd x 0ul 4UL;
  pop_frame()

let main (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  root_alias()
