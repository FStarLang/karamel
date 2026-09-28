open Krml

let increment name =
  CStar.Assign (
    CStar.Var "index",
    CStar.Int Constant.UInt32,
    CStar.Call (CStar.Op Constant.Add,
      [CStar.Var name; CStar.Constant (Constant.UInt32, "1")]))

let translate body =
  CStarToC11.mk_stmt (GlobalNames.mapping (GlobalNames.create ()))
    (CStar.While (CStar.Bool true, body))

let () =
  Options.auto_for_loops := true;
  let local =
    CStar.Decl ({ name = "saved"; typ = CStar.Int Constant.UInt32 }, CStar.Var "index")
  in
  (match translate [local; increment "saved"] with
   | [C11.While _] -> ()
   | _ -> failwith "loop-local increment escaped its declaration scope");
  (match translate [increment "index"] with
   | [C11.For _] -> ()
   | _ -> failwith "declaration-free loop no longer converts to for");
  Options.auto_for_loops := false;
  match translate [increment "index"] with
  | [C11.While _] -> ()
  | _ -> failwith "disabled auto-for conversion changed the loop"
