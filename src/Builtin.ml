open Ast

let prims: file =
  "Prims", [
    DType ((["Prims"], "option"), 1, Variant [
      "None", [];
      "Some", [ "v", (TBound 0, false) ]
    ]);
  ]
