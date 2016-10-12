(** Getting rid of patterns and decompiling pattern matches. *)

(* First thing: get rid of tuples, and allocate struct definitions for them. *)
module Gen = struct
  let type_defs = ref []

  let tuple (ts: typ list) =
    try
      List.assoc ts !type_defs)
    with Not_found ->
      let doc =
        let open PPrint in
        let open PrintAst in
        separate_map underscore print_typ ts
      in
      let lid = [ "K" ], KPrint.bsprintf "%a" PrintCommon.pdoc doc in
      let fields = List.mapi (fun i t ->
        Printf.sprintf "f%d" i, (t, false)
      ) ts in
      let type_def = DType (lid, Flat fields) in
      type_defs := (ts, (lid, type_def)) :: !type_defs;
      lid, type_def

  let get () =
    snd (List.split !type_defs)
end


let drop_tuples = object(self)

  inherit [unit] map

  method! etuple () typ es =
    let ts = Checker.assert_tuple typ in
    let _, type_def = Gen.tuple (List.map (self#visit_t ()) ts) in
    EFlat (List.map2 (fun (field, _) e ->
      field, self#visit () e
    ) type_def es)

  method! ttuple () ts =
    let lid, _ = Gen.tuple (List.map (self#visit_t ()) ts) in
    TQualified lid

  method pattern () t pat =
    let rec drop = function
      | (PUnit | PBool | PVar _) as p ->
          p
      | PCons (ident, ps) ->
          PCons (ident, List.map drop ps)
      | PRecord fields ->
          PRecord (List.map (fun (f, p) -> f, drop p) fields)
      | P

