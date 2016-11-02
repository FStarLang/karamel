open Ast

let prims: file =
  "Prims", [
    DType ((["Prims"], "option"), 1, Variant [
      "None", [];
      "Some", [ "v", (TBound 0, false) ]
    ]);
    DType ((["Prims"], "list"), 1, Variant [
      "Nil", [];
      "Cons", [
        "hd", (TBound 0, false);
        "tl", (TApp ((["Prims"], "list"), [TBound 0]), false)
      ]
    ])
  ]
