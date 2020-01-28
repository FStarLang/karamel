(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Generating Ctypes OCaml bindings for C declarations *)

open CStar

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
open PrintAst.Ops


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
let mk_unqual_name m (n: Ast.lident) =
  match n with
  | [ "K" ], n ->
      "t_" ^ n (* VD: might want to process this differently or alias to more user-friendly names *)
  | _ ->
      let n = GlobalNames.to_c_name m n in
      if Char.lowercase n.[0] <> n.[0] then
        String.make 1 (Char.lowercase n.[0]) ^ String.sub n 1 (String.length n - 1)
      else
        n

let mk_struct_name (m, n) = m, n ^ "_s" (* c.f. CStarToC11.mk_spec_and_declarator_t *)


(* Checking supported types for Ctypes bindings *)

let is_bindable_type lid =
  match lid with
  | [ "FStar"; "UInt128" ], "uint128"
  | "Lib" :: _, _ ->
    false
  | _ ->
    true

let special_types =
  let m = Hashtbl.create 41 in
  List.iter (fun (k, v) -> Hashtbl.add m k v) [
    ([ "C"; "String" ], "t"), "string" (* Ctypes.string is `char *` *)
  ];
  m

let find_type tbl typ default location =
  match Hashtbl.find_opt tbl typ with
  | Some r -> r
  | None ->
    if Hashtbl.mem special_types typ then
      default
    else
      Warn.fatal_error "Type %a (in %a) not found in context and special \
        handling not defined"
        plid typ plid location

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

let mk_qualified_type m (typ: Ast.lident) =
  (* m is for debug only *)
  try exp_ident (Hashtbl.find special_types typ)
  with Not_found -> exp_ident (mk_unqual_name m typ)

let rec mk_typ m = function
  | Int w -> exp_ident (PrintCommon.width_to_string w ^ "_t")
  | Pointer t -> Exp.apply (exp_ident "ptr") [(Nolabel, mk_typ m t)]
  | Void -> exp_ident "void"
  | Qualified l -> mk_qualified_type m l
  | Bool -> exp_ident "bool"
  | Function (_, return_type, parameters) -> build_foreign_fun m return_type (List.map (fun x -> {name=""; typ=x}) parameters)
  | Const t -> mk_typ m t
  | Union _
  | Array _
  | Struct _
  | Enum _ -> Warn.fatal_error "Unreachable"

and mk_extern_decl m name keyword typ: structure_item =
  mk_simple_app_decl (mk_unqual_name m name) None keyword [mk_const (GlobalNames.to_c_name m name); mk_typ m typ]

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
and mk_struct_decl m (k: structured) (name: Ast.lident) fields: structure_item list =
  let unqual_name = mk_unqual_name m name in
  let tm = mk_struct_manifest k unqual_name in
  let ctypes_structure =
    let struct_name = match k with
      | Union when !Options.anonymous_unions ->
          [], ""
      | Union
      | Struct ->
          mk_struct_name name
    in
    let struct_name = GlobalNames.to_c_name m struct_name in
    let t = Typ.mk (Ptyp_constr (mk_ident "typ", [tm])) in
    let e = mk_app (exp_ident (structured_kw k)) [mk_const struct_name] in
    let p = Pat.mk (Ppat_var (mk_sym unqual_name)) in
    mk_decl ~t p e
  in
  let suffix (m, n) suffix = m, n ^ "_" ^ suffix in
  let rec mk_field anon ((f_name, f_typ): string option * CStar.typ) =
    (* A field can be a named or an anonymous union, which needs to be handled
     * separately and generates additional declaratons, or another type, which
     * only generates the field declaration *)
    match f_typ with
    | Union fields ->
      let anon, name =
        match f_name with
        | Some field_name -> false, suffix name field_name
        | _ -> true, suffix name "val"
      in
      let fields = List.map (fun (x, y) -> (Some x, y)) fields in
      (mk_struct_decl m Union name fields) @ (mk_field anon (Some "u", Qualified name))
    | _ ->
      begin match f_name with
      | Some name ->
        let p = Pat.mk (Ppat_var (mk_sym (unqual_name ^ "_" ^ name))) in
        let c_name = if anon then  "" else name in
        let e = mk_app (exp_ident "field") [exp_ident unqual_name; mk_const c_name; mk_typ m f_typ] in
        [[Vb.mk p e] |> Str.value Nonrecursive]
      | None -> Warn.fatal_error "Unreachable" (* only unions can be anonymous *)
      end
  in
  let type_decl = Str.type_ Recursive [Type.mk ?manifest:(Some tm) (mk_sym unqual_name)] in
  let seal_decl = mk_decl (Pat.any ()) (mk_app (exp_ident "seal") [exp_ident unqual_name]) in
  [type_decl; ctypes_structure] @ (KList.map_flatten (mk_field false) fields) @ [seal_decl]

and mk_typedef m name typ =
  let type_const = match typ with
    | Int Constant.UInt8 -> Typ.mk (Ptyp_constr (mk_ident "Unsigned.UInt8.t", []))
    | Qualified t -> Typ.mk (Ptyp_constr (mk_ident (mk_unqual_name m t), []))
    | _ -> Warn.fatal_error "Unreachable"
  in
  let typ_name = mk_unqual_name m name in
  let name = GlobalNames.to_c_name m name in
  [ Str.type_ Recursive [Type.mk ?manifest:(Some type_const) (mk_sym typ_name)]
  ; mk_simple_app_decl typ_name None "typedef" [mk_typ m typ; mk_const name] ]

and build_foreign_fun m return_type parameters : expression =
  let types =
    if KList.is_empty parameters then
      [mk_typ m Void]
    else
      List.map (fun n -> mk_typ m n.typ) parameters
  in
  let returning = mk_app (exp_ident "returning") [mk_typ m return_type] in
  List.fold_right (fun t1 t2 -> mk_app (exp_ident "@->") [t1; t2]) types returning

and build_foreign_exp m name return_type parameters : expression =
  mk_app (exp_ident "foreign") [mk_const name; build_foreign_fun m return_type parameters]

let build_binding m name return_type parameters : structure_item =
  let func_name = mk_unqual_name m name in
  let name = GlobalNames.to_c_name m name in
  let e = build_foreign_exp m name return_type parameters in
  let p =
    match return_type with
    | Qualified ([ "C"; "String" ], "t") ->
        (* C_String_t is `const char *` and requires the function returning it to be marked as constant *)
        Pat.mk (Ppat_var (mk_sym ("constant " ^ func_name)))
    | _ ->
        Pat.mk (Ppat_var (mk_sym func_name))
  in
  mk_decl p e

let mk_enum_tags m name tags =
  let rec mk_tags n tags =
    match tags with
    | [] -> []
    | t :: ts ->
      let tag_name = String.concat "_" [mk_unqual_name m name; t] in
      (mk_simple_app_decl tag_name None "Unsigned.UInt8.of_int"
         [Exp.constant (Const.int n)]) :: (mk_tags (n+1) ts)
  in
  mk_tags 0 tags

let mk_ctypes_decl m (d: decl): structure =
  match d with
  | Function (_, _, return_type, name, parameters, _) ->
      (* Don't generate bindings for projectors and internal names *)
      if not (KString.starts_with (snd name) "__proj__") &&
         not (KString.starts_with (snd name) "uu___") then
        [build_binding m name return_type parameters]
      else
        []
  | Type (name, typ, _) -> begin
      match typ with
      | Struct fields  -> mk_struct_decl m Struct name fields
      | Enum tags ->
          let tags = List.map (GlobalNames.to_c_name m) tags in
          (mk_typedef m name (Int Constant.UInt8)) @ (mk_enum_tags m name tags)
      | Qualified t -> mk_typedef m name (Qualified t)
      | _ -> []
      end
  | Global (name, _, _, typ, _) -> begin
      match typ with
      | Function _ ->
        [mk_extern_decl m name "foreign" typ]
      | Pointer _ ->
        Warn.(maybe_fatal_error (GlobalNames.to_c_name m name, Warn.DropCtypesDeclaration ([], "extern *")));
        []
      | _ -> [mk_extern_decl m name "foreign_value" typ]
      end
  | External _
  | TypeForward _ -> []

let mk_include name =
  let module_name = Mod.apply (Mod.ident (mk_ident (name ^ "_bindings.Bindings"))) (Mod.ident (mk_ident (name ^ "_stubs"))) in
  Str.include_ (Incl.mk module_name)

let mk_ocaml_bind deps decls =
  let open_f = Str.open_ (Opn.mk ?override:(Some Fresh) (mk_ident "F")) in
  let includes = List.map mk_include deps in
  let module_exp = Mod.mk (Pmod_structure (open_f::(includes@decls))) in
  let functor_type = Mty.mk (Pmty_ident (mk_ident "Cstubs.FOREIGN")) in
  let functor_exp = Mod.functor_ (mk_sym "F") (Some functor_type) module_exp in
  Str.module_ (Mb.mk (mk_sym "Bindings") functor_exp)

let build_module deps program: structure =
  let m = mk_ocaml_bind deps program in
  let open_decls = List.map (fun m ->
    Str.open_ (Opn.mk ?override:(Some Fresh) (mk_ident m))) ["Ctypes"] in
  open_decls @ [m]

(* We now need to compute which declarations will be bound, and in the process:
 * - generate declarations for all the types that are reachable through said
 *   declarations, and
 * - compute accurate transitive dependencies for the sake of generating include
 *   OCaml statements.
 *
 * For that purpose, we receive:
 * - C* files, along with their transitive dependencies (as C file names);
 * - a translation map for name resolution
 * - a reverse-map that to each long ident maps its corresponding C file
 *
 * We return the filtered transitive dependencies, keeping only those for which
 * OCaml code was generated, along with generated OCaml declarations. *)
let mk_ocaml_bindings
  (files : (ident * string list * decl list) list)
  (m: (Ast.lident, Ast.ident) Hashtbl.t)
  (file_of: Ast.lident -> string option):
  (string * string list * structure_item list) list
=
  (* A multi-state traversal where Unsupported indicates that the given declaration
   * was meant to have bindings generated but ended up being skipped owing to an
   * unsupported type. *)
  let module T = struct
    type state =
    | Unvisited of CStar.decl
    | Visited
  end in
  let decl_map = Hashtbl.create 41 in
  List.iter (fun (_, _, decls) ->
    List.iter (fun d ->
      KPrint.bprintf "Adding %a to the decl map\n" plid (CStar.lid_of_decl d);
      Hashtbl.add decl_map (CStar.lid_of_decl d) (T.Unvisited d)
    ) decls
  ) files;

  (* From file name to a reversed list of declarations for that file *)
  let ocaml_decls = Hashtbl.create 41 in

  (* Register, in a suitable file, the OCaml binding for `lid` *)
  let ocaml_add lid decls =
    match file_of lid with
    | None ->
        Warn.fatal_error "Cannot register %a since we don't know what file it \
          originated from!" plid lid
    | Some file ->
        match Hashtbl.find_opt ocaml_decls file with
        | Some l -> Hashtbl.replace ocaml_decls file (decls :: l)
        | None -> Hashtbl.add ocaml_decls file [ decls ]
  in

  (* An ad-hoc iterator for the C* equivalent of TQualified *)
  let rec iter_typ f = function
    | Qualified l -> f l
    | Function (_, return_type, parameters) ->
        List.iter (iter_typ f) (return_type :: parameters)
    | Union l ->
        List.iter (fun x -> iter_typ f (snd x)) l
    | Struct l ->
        List.iter (fun x -> iter_typ f (snd x)) l
    | Pointer t
    | Array (t, _)
    | Const t ->
        iter_typ f t
    | Enum _
    | Int _
    | Void
    | Bool ->
        ()
  in

  let iter_decl f = function
    | Global (_, _, _, t, _) ->
        iter_typ f t
    | Function (_, _, t, _, bs, _) ->
        iter_typ f t;
        List.iter (fun b -> iter_typ f b.typ) bs
    | Type (_, t, _) ->
        iter_typ f t
    | _ ->
        ()
  in

  let should_bind lid = List.exists (fun p -> Helpers.pattern_matches p lid) !Options.ctypes in

  (* First phase: generate OCaml decls for all the bindings that need it. The
   * syntactic generation of binding code (the various `mk_*`) is not recursive,
   * and for a given declaration assumes that all the type declarations it
   * depends on have been suitably generated. So, we perform the recursive
   * traversal ourselves, avoiding loops and generating bindings in prefix order
   * of the traversal. *)
  let rec iter_lid call_stack lid: bool =
    if not (is_bindable_type lid) then
      (* Case 1: an unsupported type. Bail. *)
      false
    else if Hashtbl.mem special_types lid then
      (* Case 2: special treatment; no need to emit a declaration. *)
      true
    else
      (* Case 3: actual work needs to be done *)
      match Hashtbl.find_opt decl_map lid with
      | Some T.Visited ->
          true
      | Some (T.Unvisited d) ->
          Hashtbl.replace decl_map lid T.Visited;
          let faulty = ref None in
          (* Would be nice to have fold *)
          iter_decl (fun sub_lid ->
            if not (iter_lid (lid :: call_stack) sub_lid) then
              faulty := Some sub_lid;
          ) d;
          begin match !faulty with
          | Some faulty_lid  ->
              let loc = String.concat " <-- " (List.map Idents.string_of_lident call_stack) in
              Warn.(maybe_fatal_error (loc, Warn.DropCtypesDeclaration faulty_lid));
              false
          | None ->
              (* All of the lids that this declaration depends on have been
               * suitably bound with no error. Proceed with generating OCaml
               * bindings for the current declaration. *)
              ocaml_add lid (mk_ctypes_decl m d);
              true
          end
      | None ->
          false
  in

  List.iter (fun (_name, _deps, decls) ->
    List.iter (fun decl ->
      let lid = CStar.lid_of_decl decl in
      if should_bind lid then
        ignore (iter_lid [] lid)
    ) decls
  ) files;

  (* In a second phase, we collect the generated declarations, and turn them
   * into full-fledged OCaml modules. *)
  KList.filter_map (fun (name, deps, _) ->
    match Hashtbl.find_opt ocaml_decls name with
    | None -> None
    | Some decls -> 
        let decls = List.rev decls in
        let decls = List.flatten decls in
        let deps = List.filter (Hashtbl.mem ocaml_decls) deps in
        Some (name, deps, build_module deps decls)
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
  if List.length files > 0 then begin
    Driver.mkdirp (!Options.tmpdir ^ "/lib_gen");

    List.iter (fun (name, _, _) ->
      let m = mk_gen_decls name in
      let path = !Options.tmpdir ^ "/lib_gen/" ^ name ^ "_gen.ml" in
      write_ml path [m]
    ) files;

    let b = Buffer.create 1024 in
    List.iter (fun (f, ds, _) ->
      Printf.bprintf b "lib/%s_bindings.cmx: " f;
      List.iter (fun d ->
        Printf.bprintf b "lib/%s_bindings.cmx lib/%s_stubs.cmx " d d
      ) ds;
      Buffer.add_string b "\n";
      Printf.bprintf b "lib_gen/%s_gen.cmx: lib/%s_bindings.cmx\n" f f;
      Printf.bprintf b "lib_gen/%s_gen.exe: " f;
      List.iter (fun d ->
        Printf.bprintf b "lib/%s_bindings.cmx lib/%s_stubs.cmx lib/%s_c_stubs.o " d d d
      ) ds;
      Printf.bprintf b "lib/%s_bindings.cmx lib_gen/%s_gen.cmx " f f;
      Buffer.add_string b "\n"
    ) files;
    Buffer.output_buffer (open_out (!Options.tmpdir ^ "/ctypes.depend")) b
  end

let write_bindings (files: (string * string list * structure_item list) list) =
  if List.length files > 0 then
    Driver.mkdirp (!Options.tmpdir ^ "/lib");
  List.iter (fun (name, _, m) ->
    let path = !Options.tmpdir ^ "/lib/" ^ name ^ "_bindings.ml" in
    write_ml path m
  ) files
