module BoolFold

assume
val f : bool -> Dv unit

let main () =
  [@@CInline] let x = true in
  [@@CInline] let y = true in
  f (x && y);
  f (x && not y);
  f (x || y);
  f (x || not y);
  f (not x && y);
  f (not x && not y);
  f (not x || y);
  f (not x || not y);
  ()
