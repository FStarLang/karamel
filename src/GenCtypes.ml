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


(* generic AST helpers *)
let mk_const c =
  Exp.constant (Const.string c)

let mk_decl ?t p e =
  let binder =
    match t with
    | Some typ -> Pat.mk (Ppat_constraint (p, typ))
    | None -> p
  in
  [Vb.mk binder e] |> Str.value Nonrecursive

let mk_app e args =
  Exp.apply e (List.map (fun a -> (Nolabel, a)) args)

let mk_simple_app_decl (name: ident) (typ: ident option) (args: expression list): structure_item =
  let p = Pat.mk (Ppat_var (mk_sym name)) in
  let t = Option.map (fun x -> Typ.mk (Ptyp_constr (mk_ident x, []))) typ in
  let e = mk_app (exp_ident name) args in
  mk_decl ?t:t p e


let rec mk_typ = function
  | Int w -> exp_ident (PrintCommon.width_to_string w ^ "_t")
  | Pointer t -> Exp.apply (exp_ident "ptr") [(Nolabel, mk_typ t)]
  | Void -> exp_ident "void"
  | Qualified l -> exp_ident ("t_" ^ l) (* OCaml types need to be lower-cased *)
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


(* For binding structs, e.g. (in M.h)
 *   typedef struct M_point_s {
 *     uint32_t x;
 *     uint32_t y; }
 * we generate the following declarations:
 *   type t_M_point
 *   let t_M_point : t_M_point structure typ = structure "M_point_s"
 *   let point_x = field t_M_point "x" uint32_t
 *   let point_y = field t_M_point "y" uint32_t
 *   let _ = seal t_M_point *)
let mk_struct_decl module_name name fields: structure_item list =
  let typ_name = "t_" ^ name in
  let struct_name = name ^ "_s" in (* c.f. CStarToC11.mk_spec_and_declarator_t *)
  let unqual_name = KString.chop name (module_name ^ "_") in
  let ctypes_structure =
    let id = mk_ident (String.concat " " [typ_name; "structure"; "typ"]) in
    let t = Typ.mk (Ptyp_constr (id, [])) in
    let e = mk_app (exp_ident "structure") [mk_const struct_name] in
    let p = Pat.mk (Ppat_var (mk_sym typ_name)) in
    mk_decl ?t:(Some t) p e
  in
  let mk_field (f_name, f_typ) =
    match f_name with
    | Some name ->
      let p = Pat.mk (Ppat_var (mk_sym (unqual_name ^ "_" ^ name))) in
      let e = mk_app (exp_ident "field") [exp_ident typ_name; mk_const name; mk_typ f_typ] in
      [Vb.mk p e] |> Str.value Nonrecursive
    | None -> Warn.maybe_fatal_error
        ("", Warn.Unsupported "Anonymous struct fields not implemented");
      Str.eval (exp_ident "n/a")
  in
  let type_decl = Str.type_ Recursive [Type.mk (mk_sym typ_name)] in
  let seal_decl = mk_decl (Pat.any ()) (mk_app (exp_ident "seal") [exp_ident typ_name]) in
  [type_decl; ctypes_structure] @ (List.map mk_field fields) @ [seal_decl]

let build_foreign_exp name return_type parameters : expression =
  let types = List.map (fun n -> mk_typ n.typ) parameters in
  let returning = mk_app (exp_ident "returning") [mk_typ return_type] in
  let e = List.fold_right (fun t1 t2 -> mk_app (exp_ident "@->") [t1; t2]) types returning in
  mk_app (exp_ident "foreign") [mk_const name; e]

let build_binding module_name name return_type parameters : structure_item =
  let func_name = KString.chop name (module_name ^ "_") in
  let e = build_foreign_exp name return_type parameters in
  let p = Pat.mk (Ppat_var (mk_sym (func_name ^ "_"))) in
  mk_decl p e

let mk_ctypes_decl module_name (d: decl): structure =
  match d with
  | Function (_, _, return_type, name, parameters, _) ->
      (* Don't generated bindings for projectors *)
      if not (KString.starts_with name (module_name ^ "___proj__")) then
        [build_binding module_name name return_type parameters]
      else
        []
  | Type (name, typ, _) -> begin (* VD: do I need to consider flags here? *)
      match typ with
      | Struct fields  -> mk_struct_decl module_name name fields
      | _ -> []
      end
  | _ -> []

let mk_ocaml_bind module_name decls =
  KList.map_flatten
    (if_not_private (mk_ctypes_decl module_name)) decls

let build_module (module_name: ident) program: structure option =
  let modul = mk_ocaml_bind module_name program in
  let open_decls = List.map (fun m ->
    Str.open_ (Opn.mk ?override:(Some Fresh) (mk_ident m)))
    ["Ctypes"; "PosixTypes"; "Foreign"] in
  if not (KList.is_empty modul) then
    Some (open_decls @ modul)
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
    let path = Output.in_tmp_dir name ^ "_bindings.ml" in
    Format.set_formatter_out_channel (open_out_bin path);
    structure Format.std_formatter (migration.copy_structure m);
    Format.pp_print_flush Format.std_formatter ();
    name
  ) files
