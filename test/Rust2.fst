module Rust2

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.HyperStack.ST

#set-options "--fuel 0 --ifuel 0"
(*
let basic1 (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca 0ul 6ul in
  let x0 = B.sub x 0ul 2ul in
  let x1 = B.sub x 2ul 2ul in
  B.upd x0 0ul 1ul;
  B.upd x1 0ul 1ul;
  B.upd x 0ul 1ul;
  pop_frame ()

(*
let basic2 (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca 0ul 6ul in
  let x0 = B.sub x 0ul 2ul in
  let x1 = B.sub x 2ul 2ul in
  B.upd x0 0ul 1ul;
  B.upd x1 0ul 1ul;
  B.upd x 0ul 1ul;
  let x0 = B.sub x 0ul 2ul in
  let x1 = B.sub x 2ul 2ul in
  B.upd x0 0ul 2ul;
  B.upd x1 0ul 2ul;
  pop_frame ()
*)

let basic_copy1 (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca 0ul 6ul in
  let y = B.alloca 1ul 6ul in
  B.blit y 0ul x 0ul 6ul;
  pop_frame()
*)
let basic_copy2 (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca 0ul 6ul in
  let y = B.alloca 1ul 6ul in
  let x0 = B.sub x 0ul 2ul in
  let x1 = B.sub x0 0ul 1ul in
  // let x2 = B.sub x 1ul 4ul in
  let y0 = B.sub y 0ul 2ul in

  let y1 = B.sub y 0ul 1ul in
  // B.upd x0 0ul 5ul;
  // B.upd y0 0ul 5ul;
  B.upd x1 0ul 5ul;
  B.upd y1 0ul 5ul;
  B.blit y0 0ul x0 0ul 2ul;
  pop_frame()

(*
let doesnt_work (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca 0ul 6ul in
  let x0 = B.sub x 0ul 2ul in
  let x1 = B.sub x 2ul 2ul in
  B.upd x0 0ul 1ul;
  B.upd x1 0ul 1ul;
  B.upd x 0ul 1ul;
  B.upd x0 0ul 2ul;
  B.upd x1 0ul 2ul;
  pop_frame ()
*)

let main (): ST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
//   basic1 ();
// //  basic2 ();
//   basic_copy1();
  basic_copy2()
//  doesnt_work ()
