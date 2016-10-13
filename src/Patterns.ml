(** Getting rid of patterns and decompiling pattern matches. *)

open Ast

(* First thing: get rid of tuples, and allocate struct definitions for them. *)
module Gen = struct
  let type_defs = ref []

  let nth_field i =
    match i with
    | 0 -> "fst"
    | 1 -> "snd"
    | 2 -> "thd"
    | _ -> Printf.sprintf "f%d" i

  let ns = [ "K" ]

  let tuple (ts: typ list) =
    try
      List.assoc ts !type_defs
    with Not_found ->
      let doc =
        let open PPrint in
        let open PrintAst in
        separate_map underscore print_typ ts
      in
      let lid = ns, KPrint.bsprintf "%a" PrintCommon.pdoc doc in
      let fields = List.mapi (fun i t ->
        nth_field i, (t, false)
      ) ts in
      let type_def = DType (lid, Flat fields) in
      type_defs := (ts, (lid, type_def)) :: !type_defs;
      lid, type_def

  let clear () =
    let r = List.rev_map (fun (_, (_, d)) -> d) !type_defs in
    type_defs := [];
    r
end


let record_of_tuple = object(self)

  inherit [unit] map

  (* Generated pair declarations are inserted exactly in the right spot and
   * spread out throughout the various files, as needed. Since a given file
   * includes the header of ALL the files that precede it in the topological
   * order, then it should be fine (famous last words). *)
  method! visit_file () file =
    let name, decls = file in
    name, KList.map_flatten (fun d ->
      let d = self#visit_d () d in
      Gen.clear () @ [ d ]
    ) decls

  method! etuple () _ es =
    EFlat (List.mapi (fun i e ->
      Gen.nth_field i, self#visit () e
    ) es)

  method! ttuple () ts =
    let lid, _ = Gen.tuple (List.map (self#visit_t ()) ts) in
    TQualified lid

  method! ptuple () _ pats =
    PRecord (List.mapi (fun i p -> Gen.nth_field i, self#visit_pattern () p) pats)

end

let drop_tuples files =
  let files = Simplify.visit_files () record_of_tuple files in
  files


(** Second thing: handle the trivial case of a data type definition with only
 * tags (it's just an enum) and the trivial case of a type definition with one
 * branch (it's just a flat record). *)

type optim = ToEnum | ToFlat of ident list

let mk_tag_lid type_lid cons =
  let prefix, name = type_lid in
  (prefix @ [ name ], cons)

let optimize_visitor map = object(self)

  inherit [unit] map

  method econs () typ cons args =
    let lid = match typ with TQualified lid -> lid | _ -> assert false in
    match Hashtbl.find map lid with
    | exception Not_found ->
        ECons (cons, List.map (self#visit ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        EEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        EFlat (List.map2 (fun n e -> n, e) names args)

  method pcons () typ cons args =
    let lid = match typ with TQualified lid -> lid | _ -> assert false in
    match Hashtbl.find map lid with
    | exception Not_found ->
        PCons (cons, List.map (self#visit_pattern ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        PEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        PRecord (List.map2 (fun n e -> n, e) names args)

  method dtypevariant () lid branches =
    match Hashtbl.find map lid with
    | exception Not_found ->
        DType (lid, Variant branches)
    | ToEnum ->
        DType (lid, Enum (List.map (fun (cons, _) -> mk_tag_lid lid cons) branches))
    | ToFlat _ ->
        DType (lid, Flat (snd (List.hd branches)))
end


let optimize files =
  let map = Inlining.build_map files (fun map -> function
    | DType (lid, Variant branches) ->
        if List.for_all (fun (_, fields) -> List.length fields = 0) branches then
          Hashtbl.add map lid ToEnum
        else if List.length branches = 1 then
          Hashtbl.add map lid (ToFlat (List.map fst (snd (List.hd branches))))
    | _ ->
        ()
  ) in
  let files = Simplify.visit_files () (optimize_visitor map) files in
  files
