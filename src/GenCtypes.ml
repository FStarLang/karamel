(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Generating Ctypes OCaml bindings for C declarations *)

open CStar
open CStarToC11

open Migrate_parsetree
open Migrate_parsetree.Ast_405
open Migrate_parsetree.Ast_405.Parsetree

open Lexing
open Pprintast
open Ast_helper
open Asttypes
open Location
open Longident

(* helper functions for generating names and paths *)
let no_position : Lexing.position =
  {pos_fname = ""; pos_lnum = 0; pos_bol = 0; pos_cnum = 0}

let no_location : Location.t =
  {loc_start = no_position; loc_end = no_position; loc_ghost = false}

let no_attrs: attributes = []

let mk_sym s: string Location.loc = {txt=s; loc=no_location}

let mk_sym_ident s: Longident.t Location.loc = {txt=s; loc=no_location}

let mk_ident name = Lident name |> mk_sym_ident

let exp_ident n = Exp.ident (mk_ident n)


let rec mk_typ = function
  | Int w -> exp_ident (PrintCommon.width_to_string w ^ "_t")
  | Pointer t -> Exp.apply (exp_ident "ptr") [(Nolabel, mk_typ t)]
  | Void -> exp_ident "void"
  | Qualified l -> exp_ident l
  | Bool -> exp_ident "bool"
  (* TODO *)
  | Array _
  | Function _
  | Struct _
  | Enum _
  | Union _
  | Const _ ->
    Warn.maybe_fatal_error
      ("", Warn.Unsupported "Ctypes binding generation not implemented for this type");
    exp_ident "n/a"

let build_foreign_exp name return_type parameters : expression =
  let types = List.map (fun n -> mk_typ n.typ) parameters in
  let returning =
    Exp.apply (exp_ident "returning")
      [(Nolabel, mk_typ return_type)]
  in
  let fold_fun t1 t2 =
    Exp.apply (exp_ident "@->")
      [(Nolabel, t1); (Nolabel, t2)]
  in
  let e = List.fold_right fold_fun types returning in
  Exp.apply (exp_ident "foreign")
    [(Nolabel, Exp.constant (Const.string name)); (Nolabel, e)]

let build_binding module_name name return_type parameters : structure_item =
  let func_name = KString.chop name (module_name ^ "_") in
  let e = build_foreign_exp name return_type parameters in
  let p = Pat.mk (Ppat_var (mk_sym (func_name ^ "_"))) in
  [Vb.mk p e] |> Str.value Nonrecursive

let mk_ctypes_decl module_name (d: decl): structure =
  match d with
  | Function (_, _, return_type, name, parameters, _) ->
      [build_binding module_name name return_type parameters]
  | _ -> []

let mk_ocaml_bind module_name decls =
  KList.map_flatten
    (if_not_private (mk_ctypes_decl module_name)) decls

let build_module (module_name: ident) program: structure option =
  let modul = mk_ocaml_bind module_name program in
  let open_ctypes = Str.open_ (Opn.mk ?override:(Some Fresh) (mk_ident "Ctypes")) in
  if not (KList.is_empty modul) then
    Some (open_ctypes :: modul)
  else
    None

let mk_ocaml_bindings files: (string * string list * structure_item list) list =
  KList.map_flatten (fun (name, deps, program) ->
    if List.exists (fun p -> Bundle.pattern_matches p name) !Options.ctypes then
      match build_module name program with
      | Some m -> [(name, deps, m)]
      | None -> []
    else
      []
  ) files

let write_ml (files: (string * string list * structure_item list) list) =
  let migration = Versions.migrate Versions.ocaml_405 Versions.ocaml_current in
  List.map (fun (name, _, m) ->
    let path = Output.in_tmp_dir name ^ ".ml" in
    Format.set_formatter_out_channel (open_out_bin path);
    structure Format.std_formatter (migration.copy_structure m);
    Format.pp_print_flush Format.std_formatter ();
    name
  ) files
