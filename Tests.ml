let _ =
  Printf.printf "Printing with w=%d\n" Utils.twidth;
  let open CStar in
  let open Constant in
  let open PPrint in
  let p_t t =
    let d: CStar.decl = Type ("t", t, false) in
    let d = CStarToC.mk_stub_or_function d in
    match d with
    | Some (C.Decl ([], d)) ->
        Print.print (group (PrintC.p_declaration d));
        print_newline ()
    | _ ->
        assert false
  in
  let p_f ret args =
    let d: CStar.decl = Function (None, [], ret, "f", List.mapi (fun i t ->
      { name = Printf.sprintf "x%d" i; typ = t }
    ) args, [ Abort "test" ]) in
    let d = Option.must (CStarToC.mk_decl_or_function d) in
    Print.print (group (PrintC.p_decl_or_function d));
    print_newline ();
    print_endline (C.show_declaration_or_function d)
  in
  let t: CStar.typ = Array (Pointer (Int UInt8), Constant (UInt8, "4")) in
  p_t t;
  let t: CStar.typ = Pointer (Array (Int UInt8, Constant (UInt8, "4"))) in
  p_t t;
  let t: CStar.typ = Pointer (Function (None, Pointer (Array (Int UInt8, Constant (UInt8, "3"))), [Int UInt32])) in
  p_t t;
  let t: CStar.typ = Pointer (Function (None, Struct ([ Some "bar", Int UInt8 ]), [Int UInt32])) in
  p_t t;
  let uint8_to_uint8 = Function (None, Int UInt8, [ Int UInt8 ]) in
  p_f uint8_to_uint8 [ uint8_to_uint8 ];
;;
