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

  let rec compute_depth lid (d: type_def) =
    if not (Hashtbl.mem seen lid) && d <> Forward then
      Hashtbl.add seen lid (depth_of_def d)

  and depth_of_def d =
    match d with
    | Abbrev t ->
        depth_of_type t
    | Flat fields ->
        1 + KList.max (List.map (fun (_, (t, _)) -> depth_of_type t) fields)
    | Forward
    | Variant _ ->
        failwith "impossible"
    | Enum _ ->
        0
    | Union fields ->
        1 + KList.max (List.map (fun (_, t) -> depth_of_type t) fields)

  and depth_of_type t =
    match t with
    | TArrow _
    | TInt _ | TBool | TUnit | TAny | TBuf _ | TArray _ ->
        0
    | TQualified lid ->
        begin
          try depth_of_def (Hashtbl.find def_map lid)
          with Not_found -> 0
        end
    | TApp _ | TBound _ ->
        failwith "impossible"
    | TTuple ts ->
        KList.max (List.map depth_of_type ts)
    | TAnonymous def ->
        depth_of_def def
  in

  (object (_)
    inherit [_] iter
    method! visit_DType _ lid _ _ def =
      compute_depth lid def
  end)#visit_files () files;

  let l = Hashtbl.fold (fun lid depth acc -> (depth, lid) :: acc) seen [] in
  let l = List.sort compare l in

  List.iter (fun (depth, lid) ->
    KPrint.bprintf "%a: %d\n" plid lid depth
  ) l
