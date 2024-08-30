module InlineLet

(* None of {foobar,temp_x,temp_y} should appear in the output *)

let main () =
  let open FStar.Int32 in
  [@@CInline] let foobar = 0l in
  add foobar 0l

let foo (a:UInt32.t) =
  let open FStar.UInt32 in
  [@@CInline] let temp_x = a in
  [@@CInline] let temp_y = a in
  temp_x `add_underspec` temp_y
