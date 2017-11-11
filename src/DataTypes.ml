(** Monormophization of data types, including tuples, then compilation of
 * pattern matches and of data types into structs & unions. *)

open Ast
open DeBruijn
open PrintAst.Ops
open Helpers

module K = Constant

(* Zero-est thing: we need to be able to type-check the program without casts on
 * scrutinees, otherwise we won't be able to resolve anything. *)

let drop_match_cast files =
  visit_files () (object
    inherit [unit] map

    method ematch () _ e branches =
      match e.node with
      | ECast (e, _) ->
          EMatch (e, branches)
      | _ ->
          EMatch (e, branches)

  end) files



(** We need to keep track of which optimizations we performed on which data
 * types... to this effect, we build a map that assigns to each lid the type of
 * compilation scheme we adopt. Keep in mind that not all [lid]s are in the map,
 * only those that were a data type in the first place.
 *
 * New: the second component of the map is a hashtbl so that we can memoize the
 * enums that we have generated across phases. It may be the case that:
 * - option<any> becomes enum { Some, None }, because unit elimination --
 *   generates an lid for { Some, None } in the simple matches phase
 * - option<uint8> also needs the same set of tags in the general match
 *   compilation phase -- we don't want to declare a new type because that would
 *   cause collisions in the global C scope of enum components. *)
type scheme =
  | ToEnum
  | ToFlat of ident list
  | ToTaggedUnion of branches_t

let build_scheme_map files =
  build_map files (fun map -> function
    | DType (lid, _, 0, Variant branches) ->
        if List.for_all (fun (_, fields) -> List.length fields = 0) branches then
          Hashtbl.add map lid ToEnum
        else if List.length branches = 1 then
          Hashtbl.add map lid (ToFlat (List.map fst (snd (List.hd branches))))
        else
          Hashtbl.add map lid (ToTaggedUnion branches)
    | _ ->
        ()
  ), Hashtbl.create 41

(** Second thing: handle the trivial case of a data type definition with only
 * tags (it's just an enum) and the trivial case of a type definition with one
 * branch (it's just a flat record), i.e. the first two cases of [scheme] *)

let mk_tag_lid type_lid cons =
  let prefix, _ = type_lid in
  prefix, cons

let try_mk_switch e branches =
  (* TODO if the last case is a PWild then make it the default case of the
   * switch *)
  try
    ESwitch (e, List.map (fun (_, pat, e) ->
      match pat.node with
      | PEnum lid -> lid, e
      | _ -> raise Exit
    ) branches)
  with Exit ->
    EMatch (e, branches)

let is_trivial_record_pattern fields =
  List.for_all (function (_, { node = PBound _; _ }) -> true | _ -> false) fields

let try_mk_flat e t branches =
  match branches with
  | [ binders, { node = PRecord fields; _ }, body ] ->
      if is_trivial_record_pattern fields then
        (* match e with { f = x; ... } becomes
         * let tmp = e in let x = e.f in *)
        let binders, body = open_binders binders body in
        let scrut, atom = mk_binding "scrut" e.typ in
        let bindings = List.map2 (fun b (f, _) ->
          b, with_type b.typ (EField (atom, f))
        ) binders fields in
        ELet (scrut, e, close_binder scrut (nest bindings t body))
      else
        EMatch (e, branches)
  | _ ->
      EMatch (e, branches)

type cached_lid =
  | Found of lident
  | Fresh of decl

(* We cache sets of tags assigned to a given enum so that there's no collisions
 * in the global scope. *)
let allocate_tag enums preferred_lid tags =
  match Hashtbl.find enums tags with
  | lid ->
      Found lid
  | exception Not_found ->
      Hashtbl.add enums tags preferred_lid;
      Fresh (DType (preferred_lid, [], 0, Enum tags))

let compile_simple_matches (map, enums) = object(self)

  inherit [unit] map

  val pending = ref []

  method! visit_file ok file =
    let name, decls = file in
    name, KList.map_flatten (fun d ->
      let d = self#visit_d ok d in
      let new_decls = !pending in
      pending := [];
      new_decls @ [ d ]
    ) decls

  method econs () typ cons args =
    let lid =
      match typ with
      | TQualified lid -> lid
      | _ -> Warnings.fatal_error "not an lid: %s: %a" cons ptyp typ
    in
    match Hashtbl.find map lid with
    | exception Not_found ->
        ECons (cons, List.map (self#visit ()) args)
    | ToTaggedUnion _ ->
        ECons (cons, List.map (self#visit ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        EEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        EFlat (List.map2 (fun n e -> Some n, self#visit () e) names args)

  method pcons () typ cons args =
    let lid =
      match typ with
      | TQualified lid -> lid
      | _ -> Warnings.fatal_error "not an lid: %s: %a" cons ptyp typ
    in
    match Hashtbl.find map lid with
    | exception Not_found ->
        PCons (cons, List.map (self#visit_pattern ()) args)
    | ToTaggedUnion _ ->
        PCons (cons, List.map (self#visit_pattern ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        PEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        PRecord (List.map2 (fun n e -> n, self#visit_pattern () e) names args)

  method dtype () lid flags n def =
    match def with
    | Variant branches ->
        assert (n = 0);
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            DType (lid, flags, 0, Variant branches)
        | ToTaggedUnion _ ->
            let tags = List.map (fun (cons, _fields) -> mk_tag_lid lid cons) branches in
            (* Pre-allocate the named type for this type's tags. Has to be done
             * here so that the enum declaration is inserted in the right spot.
             * *)
            let preferred_lid = fst lid, snd lid ^ "_tags" in
            begin match allocate_tag enums preferred_lid tags with
            | Found _ -> ()
            | Fresh decl -> pending := decl :: !pending
            end;
            DType (lid, flags, 0, Variant branches)
        | ToEnum ->
            let tags = List.map (fun (cons, _fields) -> mk_tag_lid lid cons) branches in
            begin match allocate_tag enums lid tags with
            | Found other_lid ->
                DType (lid, flags, 0, Abbrev (TQualified other_lid))
            | Fresh decl ->
                decl
            end
        | ToFlat _ ->
            let fields = List.map (fun (f, t) -> Some f, t) (snd (List.hd branches)) in
            DType (lid, flags, 0, Flat fields)
        end
    | _ ->
        DType (lid, flags, n, def)

  method ematch () t e branches =
    let e = self#visit () e in
    let branches = self#branches () branches in
    match e.typ with
    | TQualified lid ->
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            (* This might be a record in the first place. *)
            try_mk_flat e t branches
        | ToTaggedUnion _ ->
            try_mk_flat e t branches
        | ToEnum ->
            try_mk_switch e branches
        | ToFlat _ ->
            try_mk_flat e t branches
        end
    | _ ->
        EMatch (e, branches)
end

(* Third step: whole-program transformation to remove unit fields. *)
let remove_unit_fields = object (self)

  inherit [unit] map

  val erasable_fields = Hashtbl.create 41
  val mutable atoms = []

  method private is_erasable = function
    | TUnit | TAny -> true
    | _ -> false

  method private default_value = function
    | TUnit -> EUnit
    | TAny -> EAny
    | _ -> assert false

  (* Modify type definitions so that fields of type unit and any are removed.
   * Remember in a table that they are removed. *)
  method! dtypevariant _ lid branches =
    let branches =
      List.map (fun (cons, fields) ->
        cons, KList.filter_mapi (fun i (f, (t, m)) ->
          if self#is_erasable t then begin
            Hashtbl.add erasable_fields (lid, cons, i) ();
            None
          end else
            Some (f, (t, m))
        ) fields
      ) branches
    in
    Variant branches

  (* As we're about to visit a pattern, we collect binders for now-defunct
   * fields, and replace them with default values in the corresponding branch. *)
  method! branch _ (binders, pat, expr) =
    let binders, pat, expr = open_branch binders pat expr in
    let pat = self#visit_pattern () pat in
    let expr = self#visit () expr in
    let binders = List.filter (fun b -> not (List.mem b.node.atom atoms)) binders in
    let pat, expr = close_branch binders pat expr in
    binders, pat, expr

  (* Catch references to pattern-bound variables whose underlying field is gone. *)
  method! eopen () t name a =
    if List.mem a atoms then
      self#default_value t
    else
      EOpen (name, a)

  (* In a constructor pattern, remove sub-patterns over erased fields and
   * remember them. *)
  method! pcons () t cons pats =
    let pats = KList.filter_mapi (fun i p ->
      if Hashtbl.mem erasable_fields (assert_tlid t, cons, i) then begin
        begin match p.node with
        | POpen (_, a) ->
            atoms <- a :: atoms
        | _ ->
            ()
        end;
        None
      end else
        Some (self#visit_pattern () p)
    ) pats in
    PCons (cons, pats)

  method! econs () t cons exprs =
    let seq = ref [] in
    let exprs = KList.filter_mapi (fun i e ->
      if Hashtbl.mem erasable_fields (assert_tlid t, cons, i) then begin
        if not (is_value e) then
          seq := (if e.typ = TUnit then e else with_unit (EIgnore (self#visit () e))) :: !seq;
        None
      end else
        Some (self#visit () e)
    ) exprs in
    let e = ECons (cons, exprs) in
    if List.length !seq > 0 then
      ESequence (List.rev_append !seq [ (with_type t e) ])
    else
      e
end

(* Fourth step: get rid of really dumb matches we don't want to go through
 * our elaborate match-compilation scheme. Also perform some other F*-specific
 * cleanups. *)

let is_special name =
  name = "scrutinee" ||
  KString.starts_with name "uu____"

let rec is_trivially_true e =
  let open Constant in
  match e.node with
  | EBool b ->
      b = true
  | EApp ({ node = EOp (K.And, Bool); _ }, [ e1; e2 ]) ->
      is_trivially_true e1 && is_trivially_true e2
  | EApp ({ node = EOp (K.Or, Bool); _ }, [ e1; e2 ]) ->
      is_trivially_true e1 || is_trivially_true e2
  | _ ->
      false

and is_trivially_false e =
  let open Constant in
  match e.node with
  | EBool b ->
      b = false
  | EApp ({ node = EOp (K.And, Bool); _ }, [ e1; e2 ]) ->
      is_trivially_false e1 || is_trivially_false e2
  | EApp ({ node = EOp (K.Or, Bool); _ }, [ e1; e2 ]) ->
      is_trivially_false e1 && is_trivially_false e2
  | _ ->
      false


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
        (* match () with () -> ... is routinely generated by F*'s extraction. *)
        (self#visit () body).node
    | _, [ [], { node = PBool true; _ }, b1; [ v ], { node = PBound 0; _ }, b2 ] when !(v.node.mark) = 0 ->
        (* An if-then-else is generated as:
         *   match e with true -> ... | uu____???? -> ...
         * where uu____???? is unused. *)
        let b1 = self#visit () b1 in
        let _, b2 = open_binder v b2 in
        let b2 = self#visit () b2 in
        if is_trivially_true e then
          b1.node
        else if is_trivially_false e then
          b2.node
        else
          EIfThenElse (e, b1, b2)
    | _ ->
        EMatch (e, self#branches () branches)

  method! branch env (binders, pat, expr) =
    let _, binders, pat, expr = List.fold_left (fun (i, binders, pat, expr) b ->
      if !(b.node.mark) = 0 && is_special b.node.name then
        i, binders, DeBruijn.subst_p pwild i pat, DeBruijn.subst any i expr
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
  | PDeref pat ->
      let scrut = mk (EBufRead (scrut, zerou32)) in
      compile_pattern env scrut pat expr
  | PConstant k ->
      [ mk_eq (fst k) scrut (mk (EConstant k)) ], expr


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
        mk (EIfThenElse (cond, e, mk (EAbort (Some "no else in F*"))))
    | (cond, e) :: bs ->
        mk (EIfThenElse (cond, e, fold_ite bs))
  in
  match e_scrut.node with
  | EOpen _ ->
      let name_scrut = e_scrut in
      let branches = List.map (compile_branch env name_scrut) branches in
      fold_ite branches
  | _ ->
      let b_scrut, name_scrut = mk_binding "scrut" e_scrut.typ in
      let branches = List.map (compile_branch env name_scrut) branches in
      mk (ELet (b_scrut, e_scrut, close_binder b_scrut (fold_ite branches)))


let assert_branches map lid =
  match Hashtbl.find map lid with
  | ToTaggedUnion branches ->
      branches
  | _ ->
      KPrint.beprintf "Not found: %a\n" plid lid;
      raise Not_found

let field_names_of_cons cons branches =
  fst (List.split (List.assoc cons branches))


(* Fifth step: implement the general transformation of data types into tagged
 * unions. *)
let compile_all_matches (map, enums) = object (self)

  inherit [unit] map

  method private tag_and_val_type lid branches =
    let tags = List.map (fun (cons, _fields) -> mk_tag_lid lid cons) branches in
    let structs = KList.filter_map (fun (cons, fields) ->
      let fields = List.map (fun (f, t) -> Some f, t) fields in
      if List.length fields > 0 then
        Some (union_field_of_cons cons, TAnonymous (Flat fields))
      else
        None
    ) branches in
    let preferred_lid = fst lid, snd lid ^ "_tags" in
    let tag_lid =
      match allocate_tag enums preferred_lid tags with
      | Found lid -> lid
      | Fresh _ -> assert false (* pre-allocate by the previous phase *)
    in
    TQualified tag_lid, TAnonymous (Union structs)

  (* A variant declaration is a struct declaration with two fields:
   * - [field_for_tag] is the field that holds the "tag" whose type is an
   *   anonymous union
   * - [field_for_union] is the field that holds the actual value determined by
   *   the tag; it is the union of several struct types, one for each
   *   constructor. *)
  method dtypevariant _env lid branches =
    let t_tag, t_val = self#tag_and_val_type lid branches in
    Flat [
      Some field_for_tag, (t_tag, false);
      Some field_for_union, (t_val, false)
    ]

  (* A pattern on a constructor becomes a pattern on a struct and one of its
   * union fields. *)
  method pcons env t cons fields =
    let lid = assert_tlid t in
    let branches = assert_branches map lid in
    let field_names = field_names_of_cons cons branches in
    let fields = List.map (self#visit_pattern env) fields in
    let record_pat = PRecord (List.combine field_names fields) in
    let t_tag, t_val = self#tag_and_val_type lid branches in
    PRecord ([
      (** This is sound because we rely on left-to-right, lazy semantics for
       * pattern-matching. So, we read the "right" field from the union only
       * after we've ascertained that we're in the right case. *)
      field_for_tag, with_type t_tag (PEnum (mk_tag_lid lid cons))
    ] @ if List.length fields > 0 then [
      field_for_union, with_type t_val (PRecord [
        union_field_of_cons cons, with_type TAny record_pat
      ])
    ] else [
    ])

  method econs env t cons exprs =
    let lid = assert_tlid t in
    let branches = assert_branches map lid in
    let field_names = field_names_of_cons cons branches in
    let field_names = List.map (fun x -> Some x) field_names in
    let exprs = List.map (self#visit env) exprs in
    let record_expr = EFlat (List.combine field_names exprs) in
    let t_tag, t_val = self#tag_and_val_type lid branches in
    EFlat (
      [ Some field_for_tag, with_type t_tag (EEnum (mk_tag_lid lid cons)) ] @
      if List.length field_names > 0 then [
        Some field_for_union, with_type t_val (
          EFlat [ Some (union_field_of_cons cons), with_type TAny record_expr ])]
      else
        []
    )

  (* The match transformation is tricky: we open all binders. *)
  method dfunction env cc flags n ret name binders expr =
    let binders, expr = open_binders binders expr in
    let expr = self#visit env expr in
    let expr = close_binders binders expr in
    DFunction (cc, flags, n, ret, name, binders, expr)

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
   * Other matches remain (e.g. on units and booleans... [Helpers] will take
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

(* Sixth step: if the compiler supports it, use C11 anonymous structs. *)

let anonymous_unions (map, _) = object (self)
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

  method eflat env t fields =
    match fields, t with
    | [ Some f1, t1; Some f2, t2 ], TQualified lid when
      f1 = field_for_tag && f2 = field_for_union &&
      is_tagged_union map lid ->
        EFlat [ Some f1, t1; None, t2 ]
    | _ ->
        EFlat (self#fields env fields)

end

let debug_map map =
  Hashtbl.iter (fun lid scheme ->
    KPrint.bprintf "%a goes to %s\n" plid lid (
      match scheme with
      | ToEnum -> "enum"
      | ToFlat _ -> "flat"
      | ToTaggedUnion _ -> "tagged union"
    )
  ) map

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

let simplify files =
  let files = visit_files () remove_trivial_matches files in
  files

let everything files =
  let files = visit_files () remove_unit_fields files in
  let map = build_scheme_map files in
  let files = visit_files () (compile_simple_matches map) files in
  let files = visit_files () (compile_all_matches map) files in
  map, files

let anonymous_unions map files =
  visit_files () (anonymous_unions map) files
