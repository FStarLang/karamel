let _ =
  Printf.printf "Printing with w=%d\n" Utils.twidth;
  let open C in
  let open Constant in
  let open PPrint in
  let t: C.typ = Array (Pointer (Int UInt8), 4) in
  Print.print (group (PrintC.print_cstar_decl (TypeAlias ("t", t))));
  print_newline ();
  let t: C.typ = Pointer (Array (Int UInt8, 4)) in
  Print.print (group (PrintC.print_cstar_decl (TypeAlias ("t", t))));
  print_newline ();
  let t: C.typ = Pointer (Function (Pointer (Array (Int UInt8, 3)), [Int UInt32])) in
  Print.print (group (PrintC.print_cstar_decl (TypeAlias ("t", t))));
  print_newline ();
;;
