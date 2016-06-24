let _ =
  Printf.printf "Printing with w=%d\n" Utils.twidth;
  let open CStar in
  let open Constant in
  let open PPrint in
  let p t =
    let d: CStar.decl = TypeAlias ("t", t) in
    let d = CStarToC.mk_decl_or_function d in
    match d with
    | C.Decl d ->
        Print.print (group (PrintC.p_declaration d));
        print_newline ()
    | _ ->
        assert false
  in
  let t: CStar.typ = Array (Pointer (Int UInt8), Constant (UInt8, "4")) in
  p t;
  let t: CStar.typ = Pointer (Array (Int UInt8, Constant (UInt8, "4"))) in
  p t;
  let t: CStar.typ = Pointer (Function (Pointer (Array (Int UInt8, Constant (UInt8, "3"))), [Int UInt32])) in
  p t;
;;
