(* Some MSVC-specific passes / rewritings / diagnostics. *)

open Ast
open PrintAst.Ops

let types_depth files =
  let def_map = Helpers.build_map files (fun map d ->
    match d with
    | DType (lid, _, _, d) -> Hashtbl.add map lid d
    | _ -> ()
  ) in

  let seen = Hashtbl.create 41 in

  let incr (d, p) = d + 1, p in

  let rec compute_depth lid (d: type_def) =
    if not (Hashtbl.mem seen lid) && d <> Forward then
      Hashtbl.add seen lid (depth_of_def [] d)

  and depth_of_def p d =
    match d with
    | Abbrev t ->
        depth_of_type p t
    | Flat fields ->
        incr (KList.max (List.map (fun (f, (t, _)) -> depth_of_type (Option.must f :: p) t) fields))
    | Forward
    | Variant _ ->
        failwith "impossible"
    | Enum _ ->
        0, List.rev p
    | Union fields ->
        incr (KList.max (List.map (fun (f, t) -> depth_of_type (f :: p) t) fields))

  and depth_of_type p t =
    match t with
    | TArrow _
    | TInt _ | TBool | TUnit | TAny | TBuf _ | TArray _ ->
        0, List.rev p
    | TQualified lid ->
        begin try
          if not (Hashtbl.mem seen lid) then
            compute_depth lid (Hashtbl.find def_map lid);
          let d, p' = Hashtbl.find seen lid in
          d, List.rev_append p p'
        with Not_found ->
          (* External type *)
          0, List.rev p
        end
    | TApp _ | TBound _ | TTuple _ ->
        failwith "impossible"
    | TAnonymous def ->
        depth_of_def p def
  in

  (object (_)
    inherit [_] iter
    method! visit_DType _ lid _ _ def =
      compute_depth lid def
  end)#visit_files () files;

  let l = Hashtbl.fold (fun lid (depth, p) acc -> (depth, p, lid) :: acc) seen [] in
  let l = List.sort compare l in

  l


type diag = {
  name: lident;
  mutable uses_nat: bool;
  mutable uses_gctype: bool;
  mutable uses_rec: bool;
  mutable uses_string: bool;
}

let fresh_diag lid = {
  name = lid;
  uses_nat = false;
  uses_gctype = false;
  uses_rec = false;
  uses_string = false
}


let check_features files =
  let is_gctype = Helpers.build_map files (fun map d ->
    if List.mem Common.GcType (flags_of_decl d) then
      Hashtbl.add map (lid_of_decl d) ()
  ) in
  let is_gctype = Hashtbl.mem is_gctype in

  let diags = ref [] in

  (object (self)
    inherit [_] iter as super

    val mutable diag = fresh_diag ([], "")

    method! visit_EQualified env lid =
      super#visit_EQualified env lid;
      if lid = diag.name then
        diag.uses_rec <- true

    method private check_tlid lid =
      if is_gctype lid then
        diag.uses_gctype <- true;
      if lid = ([ "Prims" ], "string") then
        diag.uses_string <- true

    method! visit_TInt _ w =
      if w = K.CInt then
        diag.uses_nat <- true

    method! visit_EApp env e es =
      match e.node with
      | EQualified (["C"; "String"], l) when KString.starts_with l "of_literal" ->
          ()
      | _ ->
          super#visit_EApp env e es

    method! visit_TQualified _ lid =
      self#check_tlid lid

    method! visit_TApp env lid ts =
      List.iter (self#visit_typ env) ts;
      self#check_tlid lid

    method! visit_decl env d =
      diag <- fresh_diag (lid_of_decl d);
      super#visit_decl env d;
      if diag.uses_nat || diag.uses_gctype || diag.uses_rec || diag.uses_string then
        diags := diag :: !diags
  end)#visit_files () files;

  !diags


let all files verbose =
  if verbose then begin
    (* Warn about excessively deep types. *)
    let paths = types_depth files in
    let paths = List.filter (fun (d, _, _) -> d >= 15) paths in
    if List.length paths > 0 then
      KPrint.bprintf "[diagnostics] The following C types have a nesting depth >= 15. This may \
      cause problems when using MSVC.\n";
    List.iter (fun (depth, p, lid) ->
      KPrint.bprintf "[diagnostics] %a: %d (via %s)\n" plid lid depth (String.concat "," p)
    ) paths;
    if List.length paths > 0 then
      KPrint.bprintf "\n"
  end;

  let diags = check_features files in
  let diags, warnings = List.partition (fun x -> x.uses_rec) diags in

  if verbose then begin
    if List.length diags > 0 then
      KPrint.bprintf "[diagnostics] The following declarations require your attention.\n";
    List.iter (fun { name; _ } ->
      KPrint.bprintf "[diagnostics] %a is recursive; consider using C.Loops instead or \
      -ftail-calls\n" plid name
    ) diags
  end;

  List.iter (fun { name; uses_nat; uses_gctype; uses_string; _ } ->
    if uses_nat then
      Warnings.(maybe_fatal_error ("", NeedsCompat (name,
        "it uses mathematical integers and runtime checks may fail; rewrite your \
        code to use machine integers, or if you must, use -add-include \
        '\"prims_int.h\"'; if this declaration is for specification purposes \
        only, consider marking it noextract or using -bundle \
        <name-of-the-module> to only keep reachable definitions.")));
    if uses_gctype then
      Warnings.(maybe_fatal_error ("", NeedsCompat (name,
        "it uses a garbage-collected type (e.g. list) and will leak memory; you \
        need to link with a garbage-collector; if this declaration is for \
        specification purposes only, consider marking it noextract or using \
        -bundle <name-of-the-module> to only keep reachable definitions.")));
    if uses_string then
      Warnings.(maybe_fatal_error ("", NeedsCompat (name,
        "it uses F*'s Prims.string type and will leak memory; you \
        need to link with a garbage-collector; if this declaration is for \
        specification purposes only, consider marking it noextract or using \
        -bundle <name-of-the-module> to only keep reachable definitions; if you \
        are looking to use C strings, look into C.String (in kremlib/) and Server \
        (in test/). See the KreMLin tutorial for more information.")));
  ) warnings
