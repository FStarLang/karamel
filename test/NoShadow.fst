module NoShadow

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack

open FStar.HyperStack.ST

let f x: StackInline unit (fun _ -> true) (fun _ _ _ -> true) =
  let x = U32.(x +%^ 1ul) in
  TestLib.checku32 x 1ul

let g x: StackInline unit (fun _ -> true) (fun _ _ _ -> true) =
  let x = U64.(x +%^ 1UL) in
  TestLib.checku64 x 1UL

let b (): Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

let h x y: Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  if b () then begin
    f x;
    if b () then begin
      g y
    end
  end;
  pop_frame ()

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  h 0ul 0UL;
  0l
