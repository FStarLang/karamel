(** Getting rid of patterns and decompiling pattern matches. *)

open Ast
open DeBruijn

(* Zero-est thing: we need to be able to type-check the program without casts on
 * scrutinees, otherwise we won't be able to resolve anything. *)

let drop_match_cast files =
  Simplify.visit_files () (object
    inherit [unit] map

    method ematch () _ e branches =
      match e.node with
      | ECast (e, _) ->
          EMatch (e, branches)
      | _ ->
          EMatch (e, branches)

  end) files

(* First thing: get rid of tuples, and allocate struct definitions for them. *)
module Gen = struct
  let generated_tuples = Hashtbl.create 41
  let pending_defs = ref []

  let nth_field i =
    match i with
    | 0 -> "fst"
    | 1 -> "snd"
    | 2 -> "thd"
    | _ -> Printf.sprintf "f%d" i

  let ns = [ "K" ]

  let tuple (ts: typ list) =
    try
      Hashtbl.find generated_tuples ts
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
      pending_defs := (ts, type_def) :: !pending_defs;
      Hashtbl.add generated_tuples ts lid;
      lid

  let clear () =
    let r = List.rev_map snd !pending_defs in
    pending_defs := [];
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
    let lid = Gen.tuple (List.map (self#visit_t ()) ts) in
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

type optim = ToEnum | ToFlat of ident list | Regular

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
    | Regular ->
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
    | Regular ->
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
    | Regular ->
        DType (lid, Variant branches)
    | ToEnum ->
        DType (lid, Enum (List.map (fun (cons, _) -> mk_tag_lid lid cons) branches))
    | ToFlat _ ->
        DType (lid, Flat (snd (List.hd branches)))
end

let build_map files =
  Inlining.build_map files (fun map -> function
    | DType (lid, Variant branches) ->
        if List.for_all (fun (_, fields) -> List.length fields = 0) branches then
          Hashtbl.add map lid ToEnum
        else if List.length branches = 1 then
          Hashtbl.add map lid (ToFlat (List.map fst (snd (List.hd branches))))
        else
          Hashtbl.add map lid Regular
    | _ ->
        ()
  )

let drop_simple_data_types files =
  let map = build_map files in
  let files = Simplify.visit_files () (optimize_visitor map) files in
  map, files


(** Third thing: get rid of matches in favor of bindings, if-then-else, and
 * switches. *)

let mk_switch e branches =
  ESwitch (e, List.map (fun (pat, e) ->
    match pat.node with
    | PEnum lid -> lid, e
    | _ -> failwith "Pattern not simplified to enum"
  ) branches)

let is_trivial_record_pattern fields =
  let binders = List.fold_left (fun acc (_field, pat) ->
    match acc with
    | None ->
        None
    | Some binders ->
        match pat.node with
        | PVar b ->
            Some (b :: binders)
        | _ ->
            None
  ) (Some []) fields in
  Option.map List.rev binders

let try_mk_flat e branches =
  match branches with
  | [ { node = PRecord fields; _ }, body ] ->
      begin match is_trivial_record_pattern fields with
      | Some binders ->
          (* match e with { f = x; ... } becomes
           * let tmp = e in let x = e.f in *)
          let binders, body = open_function_binders binders body in
          let scrut, atom = Simplify.mk_binding "scrut" e.typ in
          let bindings = List.map2 (fun b (f, _) ->
            b, with_type b.typ (EField (atom, f))
          ) binders fields in
          (Simplify.nest ((scrut, e) :: bindings) body).node
          
      | None ->
          EMatch (e, branches)
      end
  | _ ->
      EMatch (e, branches)


let remove_match_visitor map = object(self)

  inherit [unit] map

  method ematch () _ e branches =
    let e = self#visit () e in
    let branches = self#branches () branches in
    match e.typ with
    | TQualified lid ->
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            (* This might be a record in the first place. *)
            try_mk_flat e branches
        | Regular ->
            try_mk_flat e branches
        | ToEnum ->
            mk_switch e branches
        | ToFlat _ ->
            try_mk_flat e branches
        end
    | _ ->
        EMatch (e, branches)

end

let drop_simple_matches map files =
  let files = Simplify.visit_files () (remove_match_visitor map) files in
  files

let everything files =
  let files = drop_tuples files in
  let map, files = drop_simple_data_types files in
  let files = drop_simple_matches map files in
  files

