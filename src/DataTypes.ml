(** Getting rid of patterns and decompiling pattern matches. *)

open Ast
open DeBruijn

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


(** Second thing: handle the trivial case of a data type definition with only
 * tags (it's just an enum) and the trivial case of a type definition with one
 * branch (it's just a flat record). *)

type optim = ToEnum | ToFlat of ident list | Regular of branches_t

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
    | Regular _ ->
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
    | Regular _ ->
        PCons (cons, List.map (self#visit_pattern ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        PEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        PRecord (List.map2 (fun n e -> n, e) names args)

  method dtype () lid def =
    match def with
    | Variant branches ->
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            DType (lid, Variant branches)
        | Regular _ ->
            DType (lid, Variant branches)
        | ToEnum ->
            DType (lid, Enum (List.map (fun (cons, _) -> mk_tag_lid lid cons) branches))
        | ToFlat _ ->
            DType (lid, Flat (snd (List.hd branches)))
        end
    | _ ->
        DType (lid, def)
end

let build_map files =
  Inlining.build_map files (fun map -> function
    | DType (lid, Variant branches) ->
        if List.for_all (fun (_, fields) -> List.length fields = 0) branches then
          Hashtbl.add map lid ToEnum
        else if List.length branches = 1 then
          Hashtbl.add map lid (ToFlat (List.map fst (snd (List.hd branches))))
        else
          Hashtbl.add map lid (Regular branches)
    | _ ->
        ()
  )


(** Third thing: get rid of (trivial) matches in favor of bindings,
 * if-then-else, and switches. *)

let mk_switch e branches =
  ESwitch (e, List.map (fun (_, pat, e) ->
    match pat.node with
    | PEnum lid -> lid, e
    | _ -> failwith "Pattern not simplified to enum"
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
        | Regular _ ->
            try_mk_flat e branches
        | ToEnum ->
            mk_switch e branches
        | ToFlat _ ->
            try_mk_flat e branches
        end
    | _ ->
        EMatch (e, branches)

end


let union_field_of_cons = (^) "u_"
let field_for_tag = "tag"
let field_for_union = "val"

let mk e =
  with_type TAny e

let mk_eq w e1 e2 =
  mk (EApp (mk (EOp (K.Eq, w)), [ e1; e2 ]))

let rec compile_pattern env scrut pat expr =
  match pat.node with
  | PCons _
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
  | PBound _ ->
      failwith "pattern must've been opened"


let rec mk_conjunction = function
  | [] ->
      failwith "impossible"
  | [ e1 ] ->
      e1
  | e1 :: es ->
      mk (EApp (mk (EOp (K.BAnd, K.Bool)), [ e1; mk_conjunction es ]))

let compile_branch env scrut (binders, pat, expr): expr * expr =
  (* This should open the binders in the pattern, too... right now we're not
   * getting the same atoms here and in PVars. See Arthur's paper. *)
  let _binders, pat, expr = open_branch binders pat expr in
  (* Compile pattern also closes the binders one by one. *)
  let conditionals, expr = compile_pattern env scrut pat expr in
  mk_conjunction conditionals, expr

let compile_match env e_scrut branches =
  let b_scrut, name_scrut = Simplify.mk_binding "scrut" e_scrut.typ in
  let branches = List.map (compile_branch env name_scrut) branches in
  let rec fold_ite = function
    | [] ->
        failwith "impossible"
    | [ cond, e ] ->
        mk (EIfThenElse (cond, e, mk EAbort))
    | (cond, e) :: bs ->
        mk (EIfThenElse (cond, e, fold_ite bs))
  in
  mk (ELet (b_scrut, e_scrut, close_binder b_scrut (fold_ite branches)))


(* Fourth step: implement the general transformation of data types into tagged
 * unions. *)
let tagged_union_visitor map = object (self)

  inherit [unit] map

  (* A variant declaration is a struct declaration with two fields:
   * - [field_for_tag] is the field that holds the "tag" whose type is an
   *   anonymous union
   * - [field_for_union] is the field that holds the actual value determined by
   *   the tag; it is the union of several struct types, one for each
   *   constructor. *)
  method dtypevariant _env lid branches =
    let tags = List.map (fun (cons, _fields) -> mk_tag_lid lid cons) branches in
    let structs = List.map (fun (cons, fields) ->
      Some (union_field_of_cons cons), TAnonymous (Flat fields)
    ) branches in
    Flat [
      field_for_tag, (TAnonymous (Enum tags), false);
      field_for_union, (TAnonymous (Union structs), false)
    ]

  (* A pattern on a constructor becomes a pattern on a struct and one of its
   * union fields. *)
  method pcons _env t cons fields =
    (* We only have nominal typing for variants. *)
    let lid = match t with TQualified lid -> lid | _ -> assert false in
    let field_names =
      match Hashtbl.find map lid with
      | Regular branches ->
          fst (List.split (List.assoc cons branches))
      | _ ->
          raise Not_found
    in
    let record_pat = PRecord (List.combine field_names fields) in
    PRecord [
      (** This is sound because we rely on left-to-right, lazy semantics for
       * pattern-matching. So, we read the "right" field from the union only
       * after we've ascertained that we're in the right case. *)
      field_for_tag, with_type TAny (PEnum (mk_tag_lid lid cons));
      field_for_union, with_type TAny (PRecord [
        union_field_of_cons cons, with_type TAny record_pat
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
    match e_scrut.typ with
    | TQualified lid ->
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            KPrint.bprintf "%a not found\n" PrintAst.plid lid;
            EMatch (e_scrut, branches)
        | _ ->
            KPrint.bprintf "compiling:\n%a\n" PrintAst.pexpr
              (with_type _t_ret (EMatch (e_scrut, branches)));
            (compile_match env e_scrut branches).node
        end
    | _ ->
        EMatch (e_scrut, branches)


end

let everything files =
  let files = Simplify.visit_files () record_of_tuple files in
  let map = build_map files in
  let files = Simplify.visit_files () (optimize_visitor map) files in
  let files = Simplify.visit_files () (remove_match_visitor map) files in
  let files = Simplify.visit_files () (tagged_union_visitor map) files in
  files
