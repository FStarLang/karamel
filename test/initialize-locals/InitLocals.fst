module InitLocals

(** Test for -finitialize-locals: uninitialized local variable
    declarations should receive zero initializers. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32

let simple (): St U32.t =
  let x = 1ul in
  let y = U32.(x +%^ 2ul) in
  y

let shadow (arg: U32.t): St U32.t =
  let x = arg in
  let y = U32.(x +%^ 1ul) in
  let x = U32.(y +%^ 1ul) in
  U32.(x +%^ y)

let branch (arg: U32.t): St U32.t =
  let x = arg in
  if U32.(x >^ 0ul) then begin
    let a = U32.(x +%^ 10ul) in
    a
  end else begin
    let b = U32.(x +%^ 20ul) in
    b
  end

let with_bool (): St U32.t =
  let b = true in
  if b then 1ul else 0ul

(* Test with a struct type (pair of u32) *)
type pair = { fst: U32.t; snd: U32.t }

let with_struct (): St U32.t =
  let p = { fst = 3ul; snd = 4ul } in
  U32.(p.fst +%^ p.snd)

let main (): St Int32.t =
  let r1 = simple () in
  TestLib.checku32 r1 3ul;
  let r2 = shadow 0ul in
  TestLib.checku32 r2 3ul;
  let r3 = branch 5ul in
  TestLib.checku32 r3 15ul;
  let r4 = branch 0ul in
  TestLib.checku32 r4 20ul;
  let r5 = with_bool () in
  TestLib.checku32 r5 1ul;
  let r6 = with_struct () in
  TestLib.checku32 r6 7ul;
  0l
