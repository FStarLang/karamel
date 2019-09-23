(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Generating Ctypes OCaml bindings for C declarations *)

open CStar
open CStarToC11

module D = Driver

open Migrate_parsetree
open Migrate_parsetree.Ast_405
open Migrate_parsetree.Ast_405.Parsetree

module Driver = D

open Lexing
open Pprintast
open Ast_helper
open Asttypes
open Location
open Longident


let migration = Versions.migrate Versions.ocaml_405 Versions.ocaml_current


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

let check_supported_type n =
  if String.equal n "FStar_UInt128_uint128" then
    Warn.fatal_error "Ctypes bindings generation is not supported for code that uses uint128"


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

let mk_simple_app_decl (name: ident) (typ: ident option) (head: ident)
  (args: expression list): structure_item =
  let p = Pat.mk (Ppat_var (mk_sym name)) in
  let t = Option.map (fun x -> Typ.mk (Ptyp_constr (mk_ident x, []))) typ in
  let e = mk_app (exp_ident head) args in
  mk_decl ?t p e


(* Note: keeping the naming scheme as decided by KreMLin, in accordance with the
 * -no-prefix options. If this is the beginning of a top-level name, lower is
 * true and we force the first letter to be lowercase to abide by OCaml syntax
 * restrictions. *)
let mk_unqual_name n =
  if KString.starts_with n "K___" then
    "t_" ^ n (* VD: might want to process this differently or alias to more user-friendly names *)
  else if Char.lowercase n.[0] <> n.[0] then
    String.make 1 (Char.lowercase n.[0]) ^ String.sub n 1 (String.length n - 1)
  else
    n

let mk_struct_name n = n ^ "_s" (* c.f. CStarToC11.mk_spec_and_declarator_t *)


(* building Ctypes declarations *)
type structured =
  | Struct
  | Union

let structured_kw = function
  | Struct -> "structure"
  | Union -> "union"

let mk_struct_manifest (k: structured) t =
  let tag = match k with
    | Struct -> t
    (* unions only ever appear as anonymous fields in structs, unless the -fnoanonymous-unions is passed,
       in which case they are assigned a name *)
    | Union -> if !Options.anonymous_unions then "anonymous" else t
  in
  let row_field = Rtag(tag, no_attrs, false, []) in
  let row = Typ.variant [row_field] Closed None in
  Typ.mk (Ptyp_constr (mk_ident (structured_kw k), [row]))

let rec mk_typ module_name = function
  | Int w -> exp_ident (PrintCommon.width_to_string w ^ "_t")
  | Pointer t -> Exp.apply (exp_ident "ptr") [(Nolabel, mk_typ module_name t)]
  | Void -> exp_ident "void"
  | Qualified l -> check_supported_type l; exp_ident (mk_unqual_name l)
  | Bool -> exp_ident "bool"
  | Function (_, return_type, parameters) -> build_foreign_fun module_name return_type (List.map (fun x -> {name=""; typ=x}) parameters)
  | Union _
  | Array _
  | Struct _
  | Enum _
  | Const _ -> Warn.fatal_error "Unreachable"

and mk_extern_decl module_name name keyword typ: structure_item =
  mk_simple_app_decl (mk_unqual_name name) None keyword [mk_const name; mk_typ module_name typ]

(* For binding structs, e.g. (in header file Types.h)
 *   typedef struct Types_point_s {
 *     uint32_t x;
 *     uint32_t y; }
 * we generate the following declarations:
 *   type point = [`point] structure
 *   let point: [`point] structure = structure "Types_point_s"
 *   let point_x = field point "x" uint32_t
 *   let point_y = field point "y" uint32_t
 *   let _ = seal point *)
and mk_struct_decl (k: structured) module_name name fields: structure_item list =
  let unqual_name = mk_unqual_name name in
  let tm = mk_struct_manifest k unqual_name in
  let ctypes_structure =
    let struct_name = match k with
      | Union when !Options.anonymous_unions -> ""
      | Union
      | Struct -> mk_struct_name name
    in
    let t = Typ.mk (Ptyp_constr (mk_ident "typ", [tm])) in
    let e = mk_app (exp_ident (structured_kw k)) [mk_const struct_name] in
    let p = Pat.mk (Ppat_var (mk_sym unqual_name)) in
    mk_decl ~t p e
  in
  let rec mk_field anon ((f_name, f_typ): string option * CStar.typ) =
    (* A field can be a named or an anonymous union, which needs to be handled separately and generates
       additional declaratons, or another type, which only generates the field declaration *)
    match f_typ with
    | Union fields ->
      let anon, name =
        match f_name with
        | Some name -> false, unqual_name ^ "_" ^ name
        | _ -> true, unqual_name ^ "_val"
      in
      let fields = List.map (fun (x, y) -> (Some x, y)) fields in
      (mk_struct_decl Union module_name name fields) @ (mk_field anon (Some "u", Qualified name))
    | _ ->
      begin match f_name with
      | Some name ->
        let p = Pat.mk (Ppat_var (mk_sym (unqual_name ^ "_" ^ name))) in
        let c_name = if anon then "" else name in
        let e = mk_app (exp_ident "field") [exp_ident unqual_name; mk_const c_name; mk_typ module_name f_typ] in
        [[Vb.mk p e] |> Str.value Nonrecursive]
      | None -> Warn.fatal_error "Unreachable" (* only unions can be anonymous *)
      end
  in
  let type_decl = Str.type_ Recursive [Type.mk ?manifest:(Some tm) (mk_sym unqual_name)] in
  let seal_decl = mk_decl (Pat.any ()) (mk_app (exp_ident "seal") [exp_ident unqual_name]) in
  [type_decl; ctypes_structure] @ (KList.map_flatten (mk_field false) fields) @ [seal_decl]

and mk_typedef module_name name typ =
  let type_const = match typ with
    | Int Constant.UInt8 -> Typ.mk (Ptyp_constr (mk_ident "Unsigned.UInt8.t", []))
    | Qualified t -> Typ.mk (Ptyp_constr (mk_ident (mk_unqual_name t), []))
    | _ -> Warn.fatal_error "Unreachable"
  in
  let typ_name = mk_unqual_name name in
  [ Str.type_ Recursive [Type.mk ?manifest:(Some type_const) (mk_sym typ_name)]
  ; mk_simple_app_decl typ_name None "typedef" [mk_typ module_name typ; mk_const name] ]

and build_foreign_fun module_name return_type parameters : expression =
  let types = List.map (fun n -> mk_typ module_name n.typ) parameters in
  let returning = mk_app (exp_ident "returning") [mk_typ module_name return_type] in
  List.fold_right (fun t1 t2 -> mk_app (exp_ident "@->") [t1; t2]) types returning

and build_foreign_exp module_name name return_type parameters : expression =
  mk_app (exp_ident "foreign") [mk_const name; build_foreign_fun module_name return_type parameters]

let build_binding module_name name return_type parameters : structure_item =
  let func_name = mk_unqual_name name in
  let e = build_foreign_exp module_name name return_type parameters in
  let p = Pat.mk (Ppat_var (mk_sym func_name)) in
  mk_decl p e

let mk_enum_tags name tags =
  let rec mk_tags n tags =
    match tags with
    | [] -> []
    | t :: ts ->
      let tag_name = String.concat "_" [mk_unqual_name name; t] in
      (mk_simple_app_decl tag_name None "Unsigned.UInt8.of_int"
         [Exp.constant (Const.int n)]) :: (mk_tags (n+1) ts)
  in
  mk_tags 0 tags

let mk_ctypes_decl module_name (d: decl): structure =
  match d with
  | Function (_, _, return_type, name, parameters, _) ->
      (* Don't generate bindings for projectors and internal names *)
      if not (KString.starts_with name (module_name ^ "___proj__")) &&
         not (KString.starts_with name (module_name ^ "_uu___"))then
        [build_binding module_name name return_type parameters]
      else
        []
  | Type (name, typ, _) -> begin
      match typ with
      | Struct fields  -> mk_struct_decl Struct module_name name fields
      | Enum tags ->
        (mk_typedef module_name name (Int Constant.UInt8)) @ (mk_enum_tags name tags)
      | Qualified t -> mk_typedef module_name name (Qualified t)
      | _ -> []
      end
  | Global (name, _, _, typ, _) -> begin
      match typ with
      | Function _ -> [mk_extern_decl module_name name "foreign" typ]
      | _ -> [mk_extern_decl module_name name "foreign_value" typ]
      end
  | External _
  | TypeForward _ -> []

let mk_include name =
  let module_name = Mod.apply (Mod.ident (mk_ident (name ^ "_bindings.Bindings"))) (Mod.ident (mk_ident (name ^ "_stubs"))) in
  Str.include_ (Incl.mk module_name)

let mk_ocaml_bind module_name deps decls =
  let decls = KList.map_flatten
    (if_not_private (mk_ctypes_decl module_name)) decls
  in
  if not (KList.is_empty decls) then
    let open_f = Str.open_ (Opn.mk ?override:(Some Fresh) (mk_ident "F")) in
    let includes = List.map mk_include deps in
    let module_exp = Mod.mk (Pmod_structure (open_f::(includes@decls))) in
    let functor_type = Mty.mk (Pmty_ident (mk_ident "Cstubs.FOREIGN")) in
    let functor_exp = Mod.functor_ (mk_sym "F") (Some functor_type) module_exp in
    Some (Str.module_ (Mb.mk (mk_sym "Bindings") functor_exp))
  else
    None

let build_module (module_name: ident) deps program: structure option =
  let modul = mk_ocaml_bind module_name deps program in
  let open_decls = List.map (fun m ->
    Str.open_ (Opn.mk ?override:(Some Fresh) (mk_ident m))) ["Ctypes"] in
  Option.map (fun m -> open_decls @ [m]) modul

let module_name fn =
  if Filename.check_suffix fn "krml" then
    let fn = Filename.basename fn in
    String.sub fn 0 (String.length fn - 5)
  else
    Warn.fatal_error "Expected krml file"


module Deps = Set.Make(String)

(* Given a list of bundles, their dependencies and the declaratons they contain (`files`) and
 * a table of declarations and the F* module they originate from (`modules`), we need to decide
 * the subset of declarations for which a binding will be generated. These are:
 *   - Every delcaration from a module which is passed to the `-ctypes` option.
 *   - Every type declaration from bundles which include a module passed to the `-ctypes` option.
 *   - Every type declaration from bundles which are dependencies of bundles that contain declarations
 *     for which we generate a binding.
 * This is done in 2 passes:
 *   1) `compute_bundles` goes over each bundle and includes it in the list of bundles for which
 *      bindings will be generated if it contains any declarations originally from modules passed to `-ctypes`
 *   2) `compute_bindings` goes over each bundle and filters declarations according to the criteria above.
 *     Since the list of bundles is topologically sorted, it is processed here in reverse order to build
 *     a list of dependencies. *)
let mk_ocaml_bindings
  (files : (ident * string list * decl list) list)
  (modules : (ident, string) Hashtbl.t) :
  (string * string list * structure_item list) list =

  let rec compute_bundles files modules =
    match files with
    | [] -> []
    | (f_name, _, f_decls)::fs -> begin
       let is_extracted_bundle = List.fold_left (fun b d ->
            match (d: decl) with
            | Function (_,_,_,name,_,_)
            | Global (name,_,_,_,_)
            | Type (name,_,_) ->
                b || List.exists (fun p -> Bundle.pattern_matches p (Hashtbl.find modules name)) !Options.ctypes
            | External _
            | TypeForward _ -> false
          ) false f_decls
       in
       if is_extracted_bundle then
          f_name::(compute_bundles fs modules)
        else
          compute_bundles fs modules
     end
  in

  let compute_bindings files modules =
    let bundles = compute_bundles files modules in
    let rec compute_bundle files decls deps =
      match files with
      | [] -> []
      | (f_name, f_deps, f_decls)::fs ->
          let f_decls = List.filter (fun d ->
            match (d: decl) with
            | Function (_,_,_,name,_,_)
            | Global (name,_,_,_,_) ->
                List.exists (fun p -> Bundle.pattern_matches p (Hashtbl.find modules name)) !Options.ctypes
            | Type (name,_,_) ->
                let decl_module = Hashtbl.find modules name in
                List.exists (fun p -> Bundle.pattern_matches p decl_module) !Options.ctypes ||
                Deps.mem decl_module deps ||
                List.mem f_name bundles
            | External _
            | TypeForward _ -> false
          ) f_decls
          in
          let deps =
            if not (KList.is_empty f_decls) then
              List.fold_right Deps.add f_deps deps
            else
              deps
          in
          (f_name, f_deps, f_decls)::(compute_bundle fs decls deps)
    in
    let files = compute_bundle (List.rev files) modules (Deps.empty) in
    List.rev files
  in
  if KList.is_empty !Options.ctypes then
    []
  else
    let files = compute_bindings files modules in
    KList.map_flatten (fun (name, deps, program) ->
        match build_module name deps program with
        | Some m -> [(name, deps, m)]
        | None -> []
      ) files

let mk_gen_decls module_name =
  let mk_out_channel n =
    mk_app
      (exp_ident "Format.set_formatter_out_channel")
      [(mk_app (exp_ident "open_out_bin") [mk_const n])]
  in
  let mk_cstubs_write typ n =
    Exp.apply
      (exp_ident ("Cstubs.write_" ^ typ))
      [ (Nolabel, exp_ident "Format.std_formatter")
      ; (Labelled "prefix", mk_const "")
      ; (Nolabel, mk_app (exp_ident "module") [exp_ident (n ^ "_bindings.Bindings")]) ]
  in
  let mk_printf s = mk_app (exp_ident "Format.printf") [mk_const s] in
  let decls =
    [ mk_out_channel ("lib/" ^ module_name ^ "_stubs.ml")
    ; mk_cstubs_write "ml" module_name
    ; mk_out_channel ("lib/" ^ module_name ^ "_c_stubs.c")
    ; mk_printf (Printf.sprintf "#include \"%s.h\"\n" module_name)
    ; mk_cstubs_write "c" module_name ]
  in
  mk_decl (Pat.any ()) (KList.reduce Exp.sequence decls)


let write_ml (path: string) (m: structure_item list) =
  Format.set_formatter_out_channel (open_out_bin path);
  structure Format.std_formatter (migration.copy_structure m);
  Format.pp_print_flush Format.std_formatter ()

let write_gen_module files =
  if List.length files > 0 then
    Driver.mkdirp (!Options.tmpdir ^ "/lib_gen");
  List.iter (fun name ->
    let m = mk_gen_decls name in
    let path = !Options.tmpdir ^ "/lib_gen/" ^ name ^ "_gen.ml" in
    write_ml path [m]
  ) files

let write_bindings (files: (string * string list * structure_item list) list) =
  if List.length files > 0 then
    Driver.mkdirp (!Options.tmpdir ^ "/lib");
  List.map (fun (name, _, m) ->
    let path = !Options.tmpdir ^ "/lib/" ^ name ^ "_bindings.ml" in
    write_ml path m;
    name
  ) files
