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
  let n = GlobalNames.to_c_name m n in
  if Char.lowercase n.[0] <> n.[0] then
    String.make 1 (Char.lowercase n.[0]) ^ String.sub n 1 (String.length n - 1)
  else
    n

let mk_struct_name (m, n) = m, n ^ "_s" (* c.f. CStarToC11.mk_spec_and_declarator_t *)

(* We keep a list of types for which a binding cannot be generated because they are
 * defined using unsupported types (see below) *)
let non_bindable_types = ref []

(* Checking supported types for Ctypes bindings *)
let is_bindable_type lid =
  match lid with
  | [ "FStar"; "UInt128" ], "uint128"
  | "Lib" :: _, _ ->
    false
  | _ ->
    not (List.mem lid !non_bindable_types)

let special_types =
  let m = Hashtbl.create 41 in
  List.iter (fun (k, v) -> Hashtbl.add m k v) [
    ([ "C"; "String" ], "t"), "string" (* Ctypes.string is `char *` *)
  ];
  m

let is_abstract_struct d =
  if List.mem Common.AbstractStruct (CStar.flags_of_decl d) then
    match d with
    | Type (_, typ, _) ->
      (match typ with
       | Struct _ -> true
       | _ -> false)
    | _ -> false
  else
    false

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

let rec mk_typ ?(bytes=false) m = function
  | Int w -> exp_ident (PrintCommon.width_to_string w ^ "_t")
  | Pointer t ->
    if bytes && t = Int Constant.UInt8 then
      (* special handling for functions which take uint8_t* as arguments in order to pass OCaml Bytes.t directly *)
      exp_ident "ocaml_bytes"
    else
      Exp.apply (exp_ident "ptr") [(Nolabel, mk_typ m t)]
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
and mk_struct_decl ?(sealed=true) m (k: structured) (name: Ast.lident) fields: structure_item list =
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
  [type_decl; ctypes_structure] @ (KList.map_flatten (mk_field false) fields) @ (if sealed then [seal_decl] else [])

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
      List.map (fun n -> mk_typ m n.typ ~bytes:true) parameters
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
  let module_app = Mod.apply (Mod.ident (mk_ident (name ^ "_bindings.Bindings"))) (Mod.ident (mk_ident (name ^ "_stubs"))) in
  let module_def = Str.module_ (Mb.mk (mk_sym (name ^ "_applied")) module_app) in
  [
    module_def;
    Str.open_ (Opn.mk (mk_ident (name ^ "_applied")));
  ]

let mk_ocaml_bind deps decls =
  let open_f = Str.open_ (Opn.mk ?override:(Some Fresh) (mk_ident "F")) in
  let includes = KList.map_flatten mk_include deps in
  let module_exp = Mod.mk (Pmod_structure (open_f::(includes@decls))) in
  let functor_type = Mty.mk (Pmty_ident (mk_ident "Cstubs.FOREIGN")) in
  let functor_exp = Mod.functor_ (mk_sym "F") (Some functor_type) module_exp in
  Str.module_ (Mb.mk (mk_sym "Bindings") functor_exp)

let build_module deps program: structure =
  let m = mk_ocaml_bind deps program in
  let open_decls = List.map (fun m ->
    Str.open_ (Opn.mk ?override:(Some Fresh) (mk_ident m))) ["Ctypes"] in
  open_decls @ [m]

type t =
  (string * string list * structure_item list) list

(* We now need to visit the entire call-graph, and:
 * - generate OCaml bindings for: all the C* declarations whose lid matches a -ctypes
 *   pattern, but also all C* types that are reachable through those declarations
 * - compute accurate transitive dependencies; these determine both the open
 *   OCaml statements in the generated files, and the contents of the
 *   ctypes.depend file to aid compiling these bindings.
 *
 * For that purpose, we receive:
 * - C* files
 * - a translation map for name resolution
 * - a reverse-map that to each long ident maps its corresponding C file
 *
 * This function encapsulates all the graph-traversal logic and dependency
 * computations. Everything else in this file is concerned with OCaml syntax
 * generation.
 *
 * We return the transitive dependencies (the names of the files that contain
 * OCaml bindings, now no longer related to C/H files), along with generated
 * OCaml declarations. *)
let mk_ocaml_bindings
  (files : (ident * string list * decl list) list)
  (m: (Ast.lident, Ast.ident) Hashtbl.t)
  (file_of: Ast.lident -> string option):
  (string * string list * structure_item list) list
=
  (** A multi-state traversal of the call-graph; we map each lid to its
   * corresponding C* declaration. *)
  let module T = struct
    type state =
    | Unvisited of CStar.decl
    | Visited
  end in
  let decl_map = Hashtbl.create 41 in
  List.iter (fun (_, _, decls) ->
    List.iter (fun d ->
      Hashtbl.add decl_map (CStar.lid_of_decl d) (T.Unvisited d)
    ) decls
  ) files;

  let assert_file_of lid =
    match file_of lid with
    | None ->
        Warn.fatal_error "Cannot register %a since we don't know what file it \
          originated from!" plid lid
    | Some file ->
        file
  in

  (** Maps a given OCaml filename to a list of OCaml bindings (in reverse). *)
  let ocaml_decls = Hashtbl.create 41 in

  (* Extend the map above by adding the OCaml bindings `decls` to the file that
   * `lid` belongs to. *)
  let ocaml_add lid decls =
    let file = assert_file_of lid in
    match Hashtbl.find_opt ocaml_decls file with
    | Some l -> Hashtbl.replace ocaml_decls file (decls :: l)
    | None -> Hashtbl.add ocaml_decls file [ decls ]
  in

  (** Direct dependencies, based uniquely on the reachable set of lids via the
   * OCaml signatures. This is optimal and we thus ignore the dependencies we
   * receive (second element of the triples in `files`). *)
  let ocaml_deps = Hashtbl.create 41 in

  let remove_duplicates deps =
    let deps = List.fold_left (fun deps next ->
      if List.mem next deps then
        deps
      else
        next :: deps
    ) [] deps in
    List.rev deps
  in

  (* Extend the map above, registering a dependency from the file that contains
   * [lid] to the files where [lids] reside. *)
  let ocaml_dep lid lids =
    let source = assert_file_of lid in
    let lids = List.filter (fun x -> not (Hashtbl.mem special_types x)) lids in
    let lids = List.map assert_file_of lids in
    let curr = try Hashtbl.find ocaml_deps source with Not_found -> [] in
    let lids = List.filter ((<>) source) lids in
    Hashtbl.replace ocaml_deps source (remove_duplicates (curr @ lids))
  in

  (** Files for which we have successfully emitted declarations. *)
  let ocaml_files = ref [] in

  let ocaml_file lid = ocaml_files := String.concat "_" (fst lid) :: !ocaml_files in

  (** First phase: generate OCaml bindings for all the declarations that need it. The
   * syntactic generation of binding code (the various `mk_*`) is not recursive,
   * and for a given declaration assumes that all the type declarations it
   * depends on have been suitably generated. So, we perform the recursive
   * traversal ourselves, avoiding loops and generating bindings in prefix order
   * of the traversal. *)
  let rec iter_lid call_stack lid : bool =
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
        begin
          Hashtbl.replace decl_map lid T.Visited;
          let faulty = ref None in
          let lids = ref [] in
          (* Would be nice to have fold *)
          CStar.iter_decl (fun sub_lid ->
            if not (iter_lid (lid :: call_stack) sub_lid) then
              faulty := Some sub_lid;
              lids := sub_lid :: !lids
          ) d;
          if is_abstract_struct d then begin
            (* Wether it contains unsupported types or not, an abstract struct will be bound
             * as an empty, unsealed struct since it will only be manipulated through pointers
             * (Ctypes enforces this at runtime) *)
            ocaml_add lid (mk_struct_decl ~sealed:false m Struct lid []);
            ocaml_file lid;
            true
          end else
            (* Check if it depends on any unsupported types *)
            match !faulty with
            | Some faulty_lid  ->
              let loc = String.concat " <-- " (List.map Idents.string_of_lident call_stack) in
              non_bindable_types := lid :: !non_bindable_types;
              Warn.(maybe_fatal_error (loc, Warn.DropCtypesDeclaration faulty_lid));
              false
            | None ->
              (* All of the lids that this declaration depends on have been
               * suitably bound with no error. Proceed with generating OCaml
               * bindings for the current declaration. Also register
               * dependencies for later. *)
              ocaml_add lid (mk_ctypes_decl m d);
              ocaml_dep lid (List.rev !lids);
              ocaml_file lid;
              true
        end
      | None ->
          false
  in

  let should_bind lid flags =
    List.exists (fun p -> Helpers.pattern_matches p lid) !Options.ctypes &&
    not (List.mem Common.Private flags)
  in

  List.iter (fun (_name, _deps, decls) ->
    List.iter (fun decl ->
      let lid = CStar.lid_of_decl decl in
      let flags = CStar.flags_of_decl decl in
      if should_bind lid flags then
        ignore (iter_lid [] lid)
    ) decls
  ) files;

  (* Sanity check: no superfluous arguments to -ctypes *)
  List.iter (fun p ->
    if not (List.exists (Bundle.pattern_matches p) !ocaml_files) then
      Warn.fatal_error "Pattern %s was passed to -ctypes but no source module matches"
        (Bundle.string_of_pattern p);
  ) !Options.ctypes;

  (** In a second phase, we need to compute transitive dependencies for
   * generating the ctypes.depend file. The syntactic generation of OCaml
   * binding code assumes that all the required types are in scope, so we open
   * all the transitive dependencies. *)
  let transitive_deps = Hashtbl.create 41 in
  List.iter (fun (name, _, _) ->
    let deps = try Hashtbl.find ocaml_deps name with Not_found -> [] in
    let deps = KList.map_flatten (fun x ->
      Hashtbl.find transitive_deps x @ [ x ]
    ) deps in
    Hashtbl.add transitive_deps name (remove_duplicates deps)
  ) files;

  (** In a third phase, we collect the generated declarations, and turn them
   * into full-fledged OCaml modules. *)
  KList.filter_map (fun (name, _, _) ->
    match Hashtbl.find_opt ocaml_decls name with
    | None -> None
    | Some decls ->
        let decls = List.flatten (List.rev decls) in
        if List.length decls > 0 then begin
          let build_deps = Hashtbl.find transitive_deps name in
          Some (name, build_deps, build_module build_deps decls)
        end else
          None
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
    Printf.bprintf b "CTYPES_DEPS=";
    List.iter (fun (f, _, _) -> Printf.bprintf b "lib/%s_stubs.cmx lib/%s_bindings.cmx " f f) files;
    Buffer.add_string b "\n";
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

let file_list files =
  List.map (fun (f, _, _) -> f) files
