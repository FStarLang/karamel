module IfDef

open FStar.HyperStack.ST

[@ CIfDef ]
assume val x: bool

[@ CIfDef ]
assume val y: bool

let foo (): FStar.HyperStack.ST.Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let foo' (): FStar.HyperStack.ST.Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

let test b: FStar.HyperStack.ST.Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  if x then
    if b then
      foo ()
    else
      ()

let bar (): FStar.HyperStack.ST.Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

module IB = LowStar.ImmutableBuffer

let b: (b:IB.ibuffer bool { IB.length b = 1 /\ IB.recallable b }) =
  IB.igcmalloc_of_list HyperStack.root [ true ]

inline_for_extraction
let cond (): FStar.HyperStack.ST.Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  let uu__ = IB.recall b in
  IB.index b 0ul

let test2 () =
  let uu__b3 = cond () in
  let uu__b2 = cond () in
  let uu__b1 = cond () in
  if x && uu__b1 then
    0ul
  else if y && uu__b2 then
    1ul
  else if x && y && uu__b3 then
    2ul
  else
    3ul

(* A representative test of what we do in EverCrypt. *)
let test3 (): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  let uu__has_feature = bar () in
  if x && uu__has_feature then
    foo ()
  else
    foo' ()

let main (): Int32.t =
  if x && y then
    1l
  else if x || y then
    0l
  else
    1l
