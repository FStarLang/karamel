module Rust1

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"

let main (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca 0ul 6ul in
  let x0 = B.sub x 0ul 2ul in
  let x2 = B.sub x 4ul 2ul in
  let x1 = B.sub x 2ul 2ul in
  B.upd x0 0ul 0ul;
  B.upd x0 1ul 1ul;
  B.upd x1 0ul 2ul;
  B.upd x1 1ul 3ul;
  B.upd x2 0ul 4ul;
  B.upd x2 1ul 5ul;
  let v0 = B.index x 0ul in
  let v1 = B.index x 1ul in
  let v2 = B.index x 2ul in
  let v3 = B.index x 3ul in
  let v4 = B.index x 4ul in
  let v5 = B.index x 5ul in
  pop_frame ();
  LowStar.Printf.(printf "%ul %ul %ul %ul %ul %ul" v0 v1 v2 v3 v4 v5 done)
