module AggressiveInline

(* None of {foobar,temp_x,temp_y} should appear in the output. This is similar
to the test in InlineLet.fst, but is extracted with the `-faggressive-inling`
flag of karamel. So there is no need for the CInline attributes. *)

let main () =
  let open FStar.Int32 in
  let foobar = 0l in
  add foobar 0l

let foo (a:UInt32.t) =
  let open FStar.UInt32 in
  let temp_x = a in
  let temp_y = a in
  temp_x `add_underspec` temp_y
