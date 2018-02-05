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

  List.iter (fun (depth, p, lid) ->
    KPrint.bprintf "%a: %d (via %s)\n" plid lid depth (String.concat "," p)
  ) l
