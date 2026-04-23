module SimplifyMergeETApp

open FStar.HyperStack.ST

(* LowStar.Ignore.ignore is a polymorphic builtin whose ETApp survives
   monomorphization.  Combined with -fmerge, this exercises the ETApp
   case in SimplifyMerge. *)

let test (): St FStar.UInt32.t =
  let open FStar.UInt32 in
  let x = 1ul in
  LowStar.Ignore.ignore x;
  let y = 2ul in
  LowStar.Ignore.ignore y;
  x +%^ y

let main (): St FStar.Int32.t =
  let r = test () in
  if r = 3ul then 0l else 1l
