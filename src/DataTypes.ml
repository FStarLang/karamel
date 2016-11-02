(** Getting rid of patterns and decompiling pattern matches. *)

open Ast
open DeBruijn
open PrintAst.Ops

module K = Constant

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

(* First thing: get rid of tuples, and generate (monomorphize) struct
 * definitions for them. *)
module Gen = struct
  let generated_lids = Hashtbl.create 41
  let pending_defs = ref []

  let gen_lid lid ts =
    let doc =
      let open PPrint in
      let open PrintAst in
      separate_map underscore print_typ ts
    in
    fst lid, snd lid ^ KPrint.bsprintf "__%a" PrintCommon.pdoc doc

  let register_def original_lid ts lid def =
    let type_def = DType (lid, 0, def) in
    pending_defs := type_def :: !pending_defs;
    Hashtbl.add generated_lids (original_lid, ts) lid;
    lid

  let nth_field i =
    match i with
    | 0 -> "fst"
    | 1 -> "snd"
    | 2 -> "thd"
    | _ -> Printf.sprintf "f%d" i

  let tuple (ts: typ list) =
    let tuple_lid = [ "K" ], "" in
    try
      Hashtbl.find generated_lids (tuple_lid, ts)
    with Not_found ->
      let lid = gen_lid tuple_lid ts in
      let fields = List.mapi (fun i t ->
        Some (nth_field i), (t, false)
      ) ts in
      register_def tuple_lid ts lid (Flat fields)

  let variant original_lid branches ts =
    try
      Hashtbl.find generated_lids (original_lid, ts)
    with Not_found ->
      let lid = gen_lid original_lid ts in
      let branches = List.map (fun (cons, fields) ->
        cons, List.map (fun (field, (t, m)) ->
          field, (DeBruijn.subst_tn t ts, m)
        ) fields
      ) branches in
      register_def original_lid ts lid (Variant branches)

  let flat original_lid fields ts =
    try
      Hashtbl.find generated_lids (original_lid, ts)
    with Not_found ->
      let lid = gen_lid original_lid ts in
      let fields = List.map (fun (field, (t, m)) ->
        field, (DeBruijn.subst_tn t ts, m)
      ) fields in
      register_def original_lid ts lid (Flat fields)

  let clear () =
    let r = List.rev !pending_defs in
    pending_defs := [];
    r
end

let build_def_map files =
  Inlining.build_map files (fun map -> function
    | DType (lid, _, def) ->
        Hashtbl.add map lid def
    | _ ->
        ()
  )

let monorphize_data_types map = object(self)

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
      Some (Gen.nth_field i), self#visit () e
    ) es)

  method! ttuple () ts =
    let lid = Gen.tuple (List.map (self#visit_t ()) ts) in
    TQualified lid

  method! ptuple () _ pats =
    PRecord (List.mapi (fun i p -> Gen.nth_field i, self#visit_pattern () p) pats)

  method! tapp () lid ts =
    let ts = List.map (self#visit_t ()) ts in
    if List.length ts > 0 then
      match Hashtbl.find map lid with
      | Variant branches ->
          TQualified (Gen.variant lid branches ts)
      | Flat fields ->
          TQualified (Gen.flat lid fields ts)
      | _ ->
          TApp (lid, ts)
    else
      TApp (lid, ts)

end

let drop_parameterized_data_types =
  Inlining.filter_decls (function
    | DType (_, n, (Flat _ | Variant _)) when n > 0 ->
        None
    | d ->
        Some d
  )



(** We need to keep track of which optimizations we performed on which data
 * types... to this effect, we build a map that assigns to each lid the type of
 * compilation scheme we adopt. Keep in mind that not all [lid]s are in the map,
 * only those that were a data type in the first place. *)
type scheme =
  | ToEnum
  | ToFlat of ident list
  | ToTaggedUnion of branches_t

let build_scheme_map files =
  Inlining.build_map files (fun map -> function
    | DType (lid, 0, Variant branches) ->
        if List.for_all (fun (_, fields) -> List.length fields = 0) branches then
          Hashtbl.add map lid ToEnum
        else if List.length branches = 1 then
          Hashtbl.add map lid (ToFlat (List.map fst (snd (List.hd branches))))
        else
          Hashtbl.add map lid (ToTaggedUnion branches)
    | _ ->
        ()
  )

(** Second thing: handle the trivial case of a data type definition with only
 * tags (it's just an enum) and the trivial case of a type definition with one
 * branch (it's just a flat record), i.e. the first two cases of [scheme] *)

let mk_tag_lid type_lid cons =
  let prefix, name = type_lid in
  (prefix @ [ name ], cons)

let mk_switch e branches =
  (* TODO: this should be try_mk_switch because there may be a wildcard, or a
   * binding name, or both, and this only takes into account exhaustive matches
   * *)
  ESwitch (e, List.map (fun (_, pat, e) ->
    match pat.node with
    | PEnum lid -> lid, e
    | _ -> Warnings.fatal_error "Pattern not simplified to enum: %a" ppat pat
  ) branches)

let is_trivial_record_pattern fields =
  List.for_all (function (_, { node = PBound _; _ }) -> true | _ -> false) fields

let try_mk_flat e branches =
  match branches with
  | [ binders, { node = PRecord fields; _ }, body ] ->
      if is_trivial_record_pattern fields then
        (* match e with { f = x; ... } becomes
         * let tmp = e in let x = e.f in *)
        let binders, body = open_binders binders body in
        let scrut, atom = Simplify.mk_binding "scrut" e.typ in
        let bindings = List.map2 (fun b (f, _) ->
          b, with_type b.typ (EField (atom, f))
        ) binders fields in
        (Simplify.nest ((scrut, e) :: bindings) body).node
      else
        EMatch (e, branches)
  | _ ->
      EMatch (e, branches)

let compile_simple_matches map = object(self)

  inherit [unit] map

  method econs () typ cons args =
    let lid = match typ with TQualified lid -> lid | _ -> assert false in
    match Hashtbl.find map lid with
    | exception Not_found ->
        ECons (cons, List.map (self#visit ()) args)
    | ToTaggedUnion _ ->
        ECons (cons, List.map (self#visit ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        EEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        EFlat (List.map2 (fun n e -> Some n, e) names args)

  method pcons () typ cons args =
    let lid = match typ with TQualified lid -> lid | _ -> assert false in
    match Hashtbl.find map lid with
    | exception Not_found ->
        PCons (cons, List.map (self#visit_pattern ()) args)
    | ToTaggedUnion _ ->
        PCons (cons, List.map (self#visit_pattern ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        PEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        PRecord (List.map2 (fun n e -> n, e) names args)

  method dtype () lid n def =
    match def with
    | Variant branches ->
        assert (n = 0);
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            DType (lid, 0, Variant branches)
        | ToTaggedUnion _ ->
            DType (lid, 0, Variant branches)
        | ToEnum ->
            DType (lid, 0, Enum (List.map (fun (cons, _) -> mk_tag_lid lid cons) branches))
        | ToFlat _ ->
            let fields = List.map (fun (f, t) -> Some f, t) (snd (List.hd branches)) in
            DType (lid, 0, Flat fields)
        end
    | _ ->
        DType (lid, n, def)

  method ematch () _ e branches =
    let e = self#visit () e in
    let branches = self#branches () branches in
    match e.typ with
    | TQualified lid ->
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            (* This might be a record in the first place. *)
            try_mk_flat e branches
        | ToTaggedUnion _ ->
            try_mk_flat e branches
        | ToEnum ->
            mk_switch e branches
        | ToFlat _ ->
            try_mk_flat e branches
        end
    | _ ->
        EMatch (e, branches)

end

(* Third step: get rid of really dumb matches we don't want to go through
 * our elaborate match-compilation scheme. Also perform some other F*-specific
 * cleanups. *)

let is_special name =
  name = "scrutinee" ||
  KString.starts_with name "uu____"

let pwild = with_type TAny PWild
let eany = with_type TAny EAny

let remove_trivial_matches = object (self)

  inherit [unit] map

  method! elet () t b e1 e2 =
    match open_binder b e2 with
    | b, { node = EMatch ({ node = EOpen (_, a); _ }, branches); _ } when
      is_special b.node.name && !(b.node.mark) = 1 &&
      Atom.equal a b.node.atom ->
        self#visit_e () (EMatch (e1, branches)) t
    | _ ->
        ELet (b, self#visit () e1, self#visit () e2)

  method! ematch () _ e branches =
    match e.node, branches with
    | EUnit, [ [], { node = PUnit; _ }, body ] ->
        (self#visit () body).node
    | _, [ [], { node = PBool true; _ }, b1; [ v ], { node = PBound 0; _ }, b2 ] when !(v.node.mark) = 0 ->
        let b1 = self#visit () b1 in
        let _, b2 = open_binder v b2 in
        let b2 = self#visit () b2 in
        EIfThenElse (e, b1, b2)
    | _ ->
        EMatch (e, self#branches () branches)

  method! branch env (binders, pat, expr) =
    let _, binders, pat, expr = List.fold_left (fun (i, binders, pat, expr) b ->
      if !(b.node.mark) = 0 && is_special b.node.name then
        i, binders, DeBruijn.subst_p pwild i pat, DeBruijn.subst eany i expr
      else
        i + 1, b :: binders, pat, expr
    ) (0, [], pat, expr) (List.rev binders) in
    binders, self#visit_pattern env pat, self#visit env expr
end


(* Fourth step is the core of this module: translating data types definitions as
 * tagged unions, and compiling pattern matches. *)

let union_field_of_cons = (^) "case_"
let field_for_tag = "tag"
let field_for_union = "val"

let mk e =
  with_type TAny e

let mk_eq w e1 e2 =
  mk (EApp (mk (EOp (K.Eq, w)), [ e1; e2 ]))

let rec compile_pattern env scrut pat expr =
  match pat.node with
  | PTuple _ ->
      failwith "should've been desugared"
  | PUnit ->
      [ mk_eq K.Int8 scrut (mk EUnit) ], expr
  | PBool b ->
      [ mk_eq K.Bool scrut (mk (EBool b)) ], expr
  | PEnum lid ->
      [ mk_eq K.Int32 scrut (mk (EEnum lid)) ], expr
  | PRecord fields ->
      let conds, expr =
        List.fold_left (fun (conds, expr) (f, p) ->
          let scrut = mk (EField (scrut, f)) in
          let cond, expr = compile_pattern env scrut p expr in
          cond :: conds, expr
        ) ([], expr) fields
      in
      List.flatten (List.rev conds), expr
  | POpen (i, b) ->
      let b = with_type pat.typ {
        name = i;
        mut = false;
        mark = ref 0;
        meta = None;
        atom = b
      } in
      [], mk (ELet (b, scrut, close_binder b expr))
  | PWild ->
      [], expr
  | PBound _ ->
      failwith "pattern must've been opened"
  | PCons (ident, _) ->
      failwith ("constructor hasn't been desugared: " ^ ident)


let rec mk_conjunction = function
  | [] ->
      mk (EBool true)
  | [ e1 ] ->
      e1
  | e1 :: es ->
      mk (EApp (mk (EOp (K.And, K.Bool)), [ e1; mk_conjunction es ]))

let compile_branch env scrut (binders, pat, expr): expr * expr =
  let _binders, pat, expr = open_branch binders pat expr in
  (* Compile pattern also closes the binders one by one. *)
  let conditionals, expr = compile_pattern env scrut pat expr in
  mk_conjunction conditionals, expr

let compile_match env e_scrut branches =
  let rec fold_ite = function
    | [] ->
        failwith "impossible"
    | [ { node = EBool true; _ }, e ] ->
        e
    | [ cond, e ] ->
        mk (EIfThenElse (cond, e, mk EAbort))
    | (cond, e) :: bs ->
        mk (EIfThenElse (cond, e, fold_ite bs))
  in
  match e_scrut.node with
  | EOpen _ ->
      let name_scrut = e_scrut in
      let branches = List.map (compile_branch env name_scrut) branches in
      fold_ite branches
  | _ ->
      let b_scrut, name_scrut = Simplify.mk_binding "scrut" e_scrut.typ in
      let branches = List.map (compile_branch env name_scrut) branches in
      mk (ELet (b_scrut, e_scrut, close_binder b_scrut (fold_ite branches)))


let assert_lid t =
  (* We only have nominal typing for variants. *)
  match t with TQualified lid -> lid | _ -> assert false

let assert_branches map lid =
  match Hashtbl.find map lid with
  | ToTaggedUnion branches ->
      branches
  | _ ->
      raise Not_found

let field_names_of_cons cons branches =
  fst (List.split (List.assoc cons branches))

let tag_and_val_type lid branches =
  let tags = List.map (fun (cons, _fields) -> mk_tag_lid lid cons) branches in
  let structs = List.map (fun (cons, fields) ->
    let fields = List.map (fun (f, t) -> Some f, t) fields in
    union_field_of_cons cons, TAnonymous (Flat fields)
  ) branches in
  TAnonymous (Enum tags), TAnonymous (Union structs)


(* Fourth step: implement the general transformation of data types into tagged
 * unions. *)
let compile_all_matches map = object (self)

  inherit [unit] map

  (* A variant declaration is a struct declaration with two fields:
   * - [field_for_tag] is the field that holds the "tag" whose type is an
   *   anonymous union
   * - [field_for_union] is the field that holds the actual value determined by
   *   the tag; it is the union of several struct types, one for each
   *   constructor. *)
  method dtypevariant _env lid branches =
    let t_tag, t_val = tag_and_val_type lid branches in
    Flat [
      Some field_for_tag, (t_tag, false);
      Some field_for_union, (t_val, false)
    ]

  (* A pattern on a constructor becomes a pattern on a struct and one of its
   * union fields. *)
  method pcons env t cons fields =
    let lid = assert_lid t in
    let branches = assert_branches map lid in
    let field_names = field_names_of_cons cons branches in
    let fields = List.map (self#visit_pattern env) fields in
    let record_pat = PRecord (List.combine field_names fields) in
    let t_tag, t_val = tag_and_val_type lid branches in
    PRecord [
      (** This is sound because we rely on left-to-right, lazy semantics for
       * pattern-matching. So, we read the "right" field from the union only
       * after we've ascertained that we're in the right case. *)
      field_for_tag, with_type t_tag (PEnum (mk_tag_lid lid cons));
      field_for_union, with_type t_val (PRecord [
        union_field_of_cons cons, with_type TAny record_pat
      ])
    ]

  method econs env t cons exprs =
    let lid = assert_lid t in
    let branches = assert_branches map lid in
    let field_names = field_names_of_cons cons branches in
    let field_names = List.map (fun x -> Some x) field_names in
    let exprs = List.map (self#visit env) exprs in
    let record_expr = EFlat (List.combine field_names exprs) in
    let t_tag, t_val = tag_and_val_type lid branches in
    EFlat [
      Some field_for_tag, with_type t_tag (EEnum (mk_tag_lid lid cons));
      Some field_for_union, with_type t_val (EFlat [
        Some (union_field_of_cons cons), with_type TAny record_expr
      ])
    ]

  (* The match transformation is tricky: we open all binders. *)
  method dfunction env cc flags ret name binders expr =
    let binders, expr = open_binders binders expr in
    let expr = self#visit env expr in
    let expr = close_binders binders expr in
    DFunction (cc, flags, ret, name, binders, expr)

  method elet env _ binder e1 e2 =
    let e1 = self#visit env e1 in
    let binder, e2 = open_binder binder e2 in
    let e2 = self#visit env e2 in
    let e2 = close_binder binder e2 in
    ELet (binder, e1, e2)

  method branches env branches =
    List.map (fun (binders, pat, expr) ->
      (* Not opening the branch... since we don't have binders inside of
       * patterns. *)
      let binders, expr = open_binders binders expr in
      let pat = self#visit_pattern env pat in
      let expr = self#visit env expr in
      let expr = close_binders binders expr in
      binders, pat, expr
    ) branches

  (* Then compile patterns for those matches whose scrutinee is a data type.
   * Other matches remain (e.g. on units and booleans... [Simplify] will take
   * care of those dummy matches. *)
  method ematch env _t_ret e_scrut branches =
    let e_scrut = self#visit env e_scrut in
    let branches = self#branches env branches in
    (compile_match env e_scrut branches).node

end

let is_tagged_union map lid =
  match Hashtbl.find map lid with
  | exception Not_found ->
      false
  | ToTaggedUnion _ ->
      true
  | _ ->
      false

(* Fifth step: if the compiler supports it, use C11 anonymous structs. *)

let anonymous_unions map = object (self)
  inherit [_] map

  method efield () _t e f =
    match e.typ with
    | TQualified lid when f = field_for_union && is_tagged_union map lid ->
        let e = self#visit () e in
        e.node
    | _ ->
        EField (self#visit () e, f)

  method type_def _env lid d =
    match d, lid with
    | Flat [ Some f1, t1; Some f2, t2 ], Some lid when
      f1 = field_for_tag && f2 = field_for_union &&
      is_tagged_union map lid ->
        Flat [ Some f1, t1; None, t2 ]
    | _ ->
        d

  method eflat _env t fields =
    match fields, t with
    | [ Some f1, t1; Some f2, t2 ], TQualified lid when
      f1 = field_for_tag && f2 = field_for_union &&
      is_tagged_union map lid ->
        EFlat [ Some f1, t1; None, t2 ]
    | _ ->
        EFlat fields

end

let everything files =
  let map = build_def_map files in
  let files = Simplify.visit_files () (monorphize_data_types map) files in
  let files = drop_parameterized_data_types files in
  let files = Simplify.visit_files [] Simplify.count_use files in
  let map = build_scheme_map files in
  let files = Simplify.visit_files () remove_trivial_matches files in
  let files = Simplify.visit_files () (compile_simple_matches map) files in
  let files = Simplify.visit_files () (compile_all_matches map) files in
  map, files

let anonymous_unions old_map files =
  (* TODO: not really clean... this is run after C name translation has occured,
   * but the map was built with original dot-names... so run this through the
   * translation table using the global state. *)
  let map = Hashtbl.create 41 in
  Hashtbl.iter (fun k v -> Hashtbl.add map (Simplify.t k) v) old_map;
  Simplify.visit_files () (anonymous_unions map) files
