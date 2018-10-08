(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(* Minimal cleanups on the generated Wasm code to compensate for our naïve
 * compilation scheme. *)

open Wasm
open CFlatToWasm

module StringMap = Map.Make(String)

let is_readonly = function
  | Ast.Const _
  | Ast.Load _
  | Ast.GetLocal _
  | Ast.GetGlobal _ ->
      true
  | _ ->
      false

let rec optimize_expr' acc es =
  match es with
  | e :: { Source.it = Ast.Drop; _ } :: es when is_readonly e.Source.it ->
      optimize_expr' acc es
  | { Source.it = Ast.If (t, e1, e2); _ } :: es ->
      let e1 = optimize_expr' [] e1 in
      let e2 = optimize_expr' [] e2 in
      optimize_expr' (dummy_phrase (Ast.If (t, e1, e2)) :: acc) es
  | { Source.it = Ast.Block (t, e); _ } :: es ->
      let e = optimize_expr' [] e in
      optimize_expr' (dummy_phrase (Ast.Block (t, e)) :: acc) es
  | { Source.it = Ast.Loop (t, e); _ } :: es ->
      let e = optimize_expr' [] e in
      optimize_expr' (dummy_phrase (Ast.Loop (t, e)) :: acc) es
  | e :: es ->
      optimize_expr' (e :: acc) es
  | [] ->
      List.rev acc

let optimize_expr (es: Ast.instr list) =
  optimize_expr' [] es

let optimize_funcs funcs =
  List.map (fun f ->
    dummy_phrase { f.Source.it with Ast.body = optimize_expr f.Source.it.Ast.body }
  ) funcs

let optimize_files files =
  List.map (fun (name, x) ->
    name, dummy_phrase { x.Source.it with Ast.funcs = optimize_funcs x.Source.it.Ast.funcs }
  ) files
