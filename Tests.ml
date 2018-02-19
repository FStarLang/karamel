let _ =
  Printf.printf "Printing with w=%d\n" Utils.twidth;
  let open CStar in
  let open Constant in
  let open PPrint in
  let p_t t =
    let d: CStar.decl = Type ("t", t, []) in
    let d = CStarToC11.mk_type_or_external d in
    match d with
    | Some (C11.Decl ([], d)) ->
        Print.print (group (PrintC.p_declaration d));
        print_newline ()
    | _ ->
        assert false
  in
  let p_f ret args =
    let d: CStar.decl = Function (None, [], ret, "f", List.mapi (fun i t -> 
      { name = Printf.sprintf "x%d" i; typ = t }
    ) args, [ Abort "test" ]) in
    let d = Option.must (CStarToC11.mk_function_or_global_body d) in
    Print.print (group (PrintC.p_decl_or_function d));
    print_newline ();
    print_endline (C11.show_declaration_or_function d)
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

open Ast
open PrintAst.Ops

class ['self] test = object (_: 'self)
  inherit [_] map
  method! visit_EBound (env, t) var =
    KPrint.bprintf "env = %s, EBound: %a = %d\n" env ptyp t var;
    EBound var
  method! visit_TUnit env =
    KPrint.bprintf "env = %s, TUnit\n" env;
    TBool
end

let _ =
   (new test)#visit_expr_w "hello" ({ node = EBound 0; typ = TUnit })
