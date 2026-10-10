(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Initialize uninitialized local variable declarations with zero values.
    Supports four modes:
    - C23: = {} (empty initializer)
    - C99: designated struct initializers (.field = init)
    - C89: positional struct initializers (no .field =) *)

module C = C11
module K = Constant

module SMap = Map.Make(String)

type mode = C23 | C99 | C89

(* A map from typedef names to their struct/union field declarations,
   built by scanning the top-level program. *)
type type_kind = TStruct | TUnion
type type_map = (type_kind * C.declaration list option) SMap.t

(* Extract the identifier name from a declarator. *)
let rec name_of_declarator (d: C.declarator): string =
  match d with
  | Ident n -> n
  | Pointer (_, d) | Array (_, d, _) | Function (_, d, _) -> name_of_declarator d

(* Build a type map from top-level declarations: maps typedef names
   to their struct fields (if any). *)
let build_type_map (program: C.program): type_map =
  List.fold_left (fun acc (df: C.declaration_or_function) ->
    match df with
    | Decl (_, (_, spec, _, Some Typedef, _, decl_inits)) ->
        let name = match decl_inits with
          | [(d, _, _)] -> Some (name_of_declarator d)
          | _ -> None
        in
        begin match name, spec with
        | Some n, Struct (_, fields) -> SMap.add n (TStruct, fields) acc
        | Some n, Union (_, fields) -> SMap.add n (TUnion, fields) acc
        | _ -> acc
        end
    | _ -> acc
  ) SMap.empty program

(* Look up a Named type in the type map. *)
let lookup_named (tmap: type_map) (name: string): (type_kind * C.declaration list) option =
  match SMap.find_opt name tmap with
  | Some (kind, Some fields) -> Some (kind, fields)
  | _ -> None

(* Generate a zero initializer for a given C11 type_spec and declarator.
   The declarator determines if we have a pointer or array wrapping. *)
let rec zero_init_for_type (mode: mode) (tmap: type_map) (spec: C.type_spec) (decl: C.declarator): C.init =
  match decl with
  | Pointer (_, _) ->
      (* Pointer type: initialize to NULL *)
      InitExpr (Name "NULL")
  | Array (_, inner, size) ->
      begin match mode with
      | C23 -> Initializer []
      | C99 | C89 ->
          (* Generate one element initializer based on the element type *)
          let elem_init = zero_init_for_type mode tmap spec inner in
          match size with
          | Some (C.Constant (_, n)) ->
              let count = try int_of_string n with _ -> 1 in
              Initializer (List.init count (fun _ -> elem_init))
          | _ ->
              (* Unknown size: single element, C will zero-fill the rest *)
              Initializer [elem_init]
      end
  | Function _ ->
      (* Function pointer if nested *)
      InitExpr (Name "NULL")
  | Ident _ ->
      (* Base case: look at the type_spec *)
      zero_init_for_spec mode tmap spec

and zero_init_for_spec (mode: mode) (tmap: type_map) (spec: C.type_spec): C.init =
  match spec with
  | Int w ->
      let s = match w with
        | K.Bool -> "false"
        | _ -> "0"
      in
      InitExpr (Constant (w, s))
  | Void ->
      InitExpr (Constant (K.Int32, "0"))
  | Named name ->
      begin match mode with
      | C23 -> Initializer []
      | C99 | C89 ->
          match lookup_named tmap name with
          | Some (TStruct, fields) -> zero_init_for_fields mode tmap fields
          | Some (TUnion, fields) -> zero_init_for_first_field mode tmap fields
          | None ->
              (* Scalar type aliases (bool, BOOLEAN, etc.) or truly unknown types *)
              let is_known_scalar = match name with
                | "bool" | "BOOLEAN" | "_Bool"
                | "size_t" | "ptrdiff_t" | "intptr_t" | "uintptr_t"
                | "int" | "unsigned" | "char" | "short" | "long"
                | "int8_t" | "int16_t" | "int32_t" | "int64_t"
                | "uint8_t" | "uint16_t" | "uint32_t" | "uint64_t"
                | "krml_checked_int_t" -> true
                | _ -> false
              in
              if is_known_scalar then
                InitExpr (Constant (K.Int32, "0"))
              else begin
                Warn.maybe_fatal_error ("", Error.InitializerUnknownType name);
                Initializer [InitExpr (Constant (K.Int32, "0"))]
              end
      end
  | Struct (_, Some fields) ->
      zero_init_for_fields mode tmap fields
  | Struct (_, None) ->
      Initializer [InitExpr (Constant (K.Int32, "0"))]
  | Union (_, Some fields) ->
      zero_init_for_first_field mode tmap fields
  | Union (_, None) ->
      Initializer [InitExpr (Constant (K.Int32, "0"))]
  | Enum _ ->
      InitExpr (Constant (K.Int32, "0"))

and zero_init_for_fields (mode: mode) (tmap: type_map) (fields: C.declaration list): C.init =
  let inits = List.concat_map (fun ((_, spec, _, _, _, decl_inits): C.declaration) ->
    List.map (fun ((d, _, _): C.declarator_and_init) ->
      let field_init = zero_init_for_type mode tmap spec d in
      match mode with
      | C99 ->
          let field_name = name_of_declarator d in
          C.Designated (C.Dot field_name, field_init)
      | C89 | C23 ->
          field_init
    ) decl_inits
  ) fields in
  Initializer inits

(* For unions, only initialize the first field. In C89, only the first field
   can be initialized; in C99, we use a designator for the first field. *)
and zero_init_for_first_field (mode: mode) (tmap: type_map) (fields: C.declaration list): C.init =
  match fields with
  | ((_, spec, _, _, _, decl_inits) : C.declaration) :: _ ->
      begin match decl_inits with
      | ((d, _, _) : C.declarator_and_init) :: _ ->
          let field_init = zero_init_for_type mode tmap spec d in
          let init = match mode with
            | C99 ->
                let field_name = name_of_declarator d in
                C.Designated (C.Dot field_name, field_init)
            | C89 | C23 ->
                field_init
          in
          Initializer [init]
      | [] -> Initializer [InitExpr (Constant (K.Int32, "0"))]
      end
  | [] -> Initializer [InitExpr (Constant (K.Int32, "0"))]

(* The top-level zero initializer for a given mode. *)
let zero_init (mode: mode) (tmap: type_map) (spec: C.type_spec) (decl: C.declarator): C.init =
  match mode with
  | C23 -> Initializer []
  | C99 | C89 -> zero_init_for_type mode tmap spec decl

let init_decl_inits (mode: mode) (tmap: type_map) (spec: C.type_spec) (decl_inits: C.declarator_and_inits): C.declarator_and_inits =
  List.map (fun ((d, align, init): C.declarator_and_init) ->
    match init with
    | None ->
        let needs_init = match d with
          | Function _ -> false
          | _ -> true
        in
        if needs_init then (d, align, Some (zero_init mode tmap spec d))
        else (d, align, init)
    | Some _ -> (d, align, init)
  ) decl_inits

let rec initialize_stmt (mode: mode) (tmap: type_map) (s: C.stmt): C.stmt =
  match s with
  | C.Compound stmts -> C.Compound (List.map (initialize_stmt mode tmap) stmts)
  | Decl (qs, spec, inline, stor, extra, decl_inits) ->
      Decl (qs, spec, inline, stor, extra, init_decl_inits mode tmap spec decl_inits)
  | If (e, s) -> If (e, initialize_stmt mode tmap s)
  | IfElse (e, s1, s2) -> IfElse (e, initialize_stmt mode tmap s1, initialize_stmt mode tmap s2)
  | IfDef (e, ss1, elifs, ss2) ->
      IfDef (e,
        List.map (initialize_stmt mode tmap) ss1,
        List.map (fun (e, ss) -> (e, List.map (initialize_stmt mode tmap) ss)) elifs,
        List.map (initialize_stmt mode tmap) ss2)
  | While (e, s) -> While (e, initialize_stmt mode tmap s)
  | For (de, e1, e2, s) ->
      let de = match de with
        | `Decl (qs, spec, inline, stor, extra, decl_inits) ->
            `Decl (qs, spec, inline, stor, extra, init_decl_inits mode tmap spec decl_inits)
        | other -> other
      in
      For (de, e1, e2, initialize_stmt mode tmap s)
  | Switch (e, cases, default) ->
      Switch (e,
        List.map (fun (e, s) -> (e, initialize_stmt mode tmap s)) cases,
        initialize_stmt mode tmap default)
  | _ -> s

let initialize_files (mode: mode) (headers: (string * C.header) list) (files: (string * C.program) list): (string * C.program) list =
  (* Build a global type map from all files and headers *)
  let tmap = List.fold_left (fun acc (_, program) ->
    SMap.union (fun _ _ v -> Some v) acc (build_type_map program)
  ) SMap.empty files in
  let tmap = List.fold_left (fun acc (_, header) ->
    let program = match header with C.Public p | C.Internal p -> p in
    SMap.union (fun _ _ v -> Some v) acc (build_type_map program)
  ) tmap headers in
  List.map (fun (name, program) ->
    let program = List.map (fun (df: C.declaration_or_function) ->
      match df with
      | Function (comments, decl, body) ->
          (Function (comments, decl, initialize_stmt mode tmap body) : C.declaration_or_function)
      | other -> other
    ) program in
    (name, program)
  ) files
