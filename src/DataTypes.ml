(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** Monormophization of data types, including tuples, then compilation of
 * pattern matches and of data types into structs & unions. *)

open Ast
open DeBruijn
open PrintAst.Ops
open Helpers

module K = Constant

(* Zero-est thing: remove unused type parameters. This increases the
 * type-ability of the code! See test/UnusedParameter.fst. *)
let remove_unused_type_arguments files =

  (* Does [lid] use its n-th type argument? This is a fixpoint computation
   * because of the mutual recursion. *)
  let uses_nth lid n =

    (* Keys are a pair of an lid and its i-th parameter. *)
    let module LidIntMap = Map.Make(struct
      type t = lident * int
      let compare = compare
    end) in
    let module ILidIntMap = MkIMap(LidIntMap) in
    let module Property = struct
      type property = bool
      let bottom = false
      let equal = (=)
      let is_maximal x = x
    end in
    let module F = Fix.Make(ILidIntMap)(Property) in

    let def_map = Helpers.build_map files (fun map d ->
      match d with
      | DType (lid, _, n, d) -> Hashtbl.add map lid (n, d)
      | _ -> ()
    ) in

    let find_ith valuation = object(self)
      inherit [_] reduce
      method zero = false
      method plus = (||)
      method expr_plus_typ = (||)

      method! visit_TBound (j, n) i =
        j = n - i - 1
      method! visit_TApp env lid args =
        let args = List.mapi (fun i arg ->
          if valuation (lid, i) then
            self#visit_typ env arg
          else
            self#zero
        ) args in
        List.fold_left self#plus self#zero args
    end in

    let equations (lid, i) valuation =
      try
        let n, def = Hashtbl.find def_map lid in
        (find_ith valuation)#visit_type_def (i, n) def
      with Not_found ->
        true
    in

    F.lfp equations (lid, n)
  in

  let remove_unused = object (self)
    inherit [_] map

    (* Then, if the i-th type parameter is unused, we remove it from the type
     * definition... *)
    method! visit_DType env lid flags n def =
      let def = self#visit_type_def env def in
      let rec chop kept i def =
        if i = n then
          kept, def
        else
          if uses_nth lid (n - i - 1) then
            chop (kept + 1) (i + 1) def
          else
            let def = (new DeBruijn.subst_t TAny)#visit_type_def i def in
            chop kept (i + 1) def
      in
      let n, def = chop 0 0 def in
      DType (lid, flags, n, def)

    (* ... and also any use of it. *)
    method! visit_TApp env lid args =
      let args = List.map (self#visit_typ env) args in
      let args = KList.filter_mapi (fun i arg ->
        if uses_nth lid i then
          Some arg
        else
          None
      ) args in
      if List.length args > 0 then
        TApp (lid, args)
      else
        TQualified lid
  end in

  Monomorphization.hints := List.map (fun ((head, args), hint) ->
    let args = List.map (remove_unused#visit_typ ()) args in
    (head, KList.filter_mapi (fun i arg -> if uses_nth head i then Some arg else None) args), hint
  ) !Monomorphization.hints;

  remove_unused#visit_files () files


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
  | Eliminate of typ
    (** Remove the data type wholesale because it has a single branch and a
     * single argument *)
  | ToEnum
  | ToFlat of ident list
  | ToTaggedUnion of branches_t
  | ToFlatTaggedUnion of branches_t
    (** Optimized scheme for data types that only have one non-constant case:
      * the tag immediately followed by the fields for the only one non-constant
      * case, possibly uninitialized *)

let one_non_constant_branch branches =
  let _constant, non_constant = List.partition (fun (_, fields) ->
    List.length fields = 0
  ) branches in
  KList.one non_constant

let build_scheme_map files =
  let map = build_map files (fun map -> function
    | DType (lid, _, 0, Variant branches) ->
        let _constant, non_constant = List.partition (fun (_, fields) ->
          List.length fields = 0
        ) branches in
        if List.length non_constant = 0 then
          Hashtbl.add map lid ToEnum
        else if List.length branches = 1 then
          Hashtbl.add map lid (ToFlat (List.map fst (snd (List.hd branches))))
        else if List.length non_constant = 1 then
          Hashtbl.add map lid (ToFlatTaggedUnion branches)
        else
          Hashtbl.add map lid (ToTaggedUnion branches);
        (* Shadow the previous binding if we *think* we can "eliminate". *)
        begin match branches with
        | [ _, [ _, (t, _ )] ] ->
            Hashtbl.add map lid (Eliminate t)
        | _ ->
            ()
        end
    | DType (lid, _, 0, Flat [ _, (t, _) ]) ->
        Hashtbl.add map lid (Eliminate t)
    | _ ->
        ()
  ) in
  (* Types that are forward-declared are not eligible for the "eliminate"
   * compilation scheme -- they are mutually recursive with another type and the
   * forward struct declaration is what allows us to compile these types. *)
  (object
    inherit [_] iter
    method visit_DType _ lid _ _ d =
      (* But if it turns out we can't eliminate, restore what otherwise would've
       * been the compilation scheme. (See OCaml doc for the behavior of add.) *)
      if d = Forward then
        match Hashtbl.find map lid with
        | exception Not_found ->
            ()
        | Eliminate _ ->
            Hashtbl.remove map lid
        | _ ->
            ()
  end)#visit_files () files;
  map, Hashtbl.create 41

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
      | PEnum lid -> SEnum lid, e
      | PConstant k -> SConstant k, e
      | PWild -> SWild, e
      | _ -> raise Exit
    ) branches)
  with Exit ->
    EMatch (e, branches)

(* An ad-hoc criterion for determining when we don't want to let-bind the
 * scrutinee of a match. *)
let rec is_simple_expression e =
  match e.node with
  | EQualified _
  | EBound _
  | EOpen _ -> true
  | EField (e, _) -> is_simple_expression e
  | _ -> false

let all_bound_variables fields =
  List.for_all (function (_, { node = PBound _; _ }) -> true | _ -> false) fields

let try_mk_flat e t branches =
  match branches with
  | [ _, { node = PRecord fields; _ }, { node = EBound i; _ } ] when
    i < List.length fields &&
    all_bound_variables fields &&
    is_simple_expression e
  ->
      let f = List.nth fields (List.length fields - i - 1) in
      EField (e, fst f)
  | [ binders, { node = PRecord fields; _ }, body ] ->
      if all_bound_variables fields then
        (* match e with { f = x; ... } becomes: *)
        let binders, body = open_binders binders body in
        if is_simple_expression e then
          (* let x0 = e.f0 in let x1 = e.f1 in ... let xn = e.fn in body *)
          let bindings = List.map2 (fun b (f, _) ->
            b, with_type b.typ (EField (e, f))
          ) binders fields in
          (nest bindings t body).node
        else
          (* let scrut = e in let x = e.f in *)
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
      (* Private will be removed, if needed, by the cross-call analysis. *)
      Fresh (DType (preferred_lid, [ Common.Private ], 0, Enum tags))

let field_for_tag = "tag"
let field_for_union = "val"

(* This does two things:
 * - deal with the simple compilation schemes (not tagged union)
 * - pre-allocate types for tags for the next phase (tagged union compilation)
 *)
let compile_simple_matches (map, enums) = object(self)

  inherit [_] map

  val pending = ref []

  method! visit_file _ file =
    let name, decls = file in
    name, KList.map_flatten (fun d ->
      let d = self#visit_decl () d in
      let new_decls = !pending in
      pending := [];
      new_decls @ [ d ]
    ) decls

  (* Warm-up: compilation of single-field __records__. *)

  method! visit_EFlat (_, typ) exprs =
    let exprs = List.map (fun (i, e) -> i, self#visit_expr_w () e) exprs in
    match Hashtbl.find map (assert_tlid typ) with
    | exception Not_found ->
        EFlat exprs
    | Eliminate _ ->
        (snd (KList.one exprs)).node
    | _ ->
        assert false

  method! visit_PRecord (_, typ) pats =
    let pats = List.map (fun (i, p) -> i, self#visit_pattern_w () p) pats in
    match Hashtbl.find map (assert_tlid typ) with
    | exception Not_found ->
        PRecord pats
    | Eliminate _ ->
        (snd (KList.one pats)).node
    | _ ->
        assert false

  method! visit_EField _ e f =
    let e' = self#visit_expr_w () e in
    match e.typ with
    | TQualified lid ->
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            EField (e', f)
        | Eliminate _ ->
            e'.node
        | _ ->
            assert false
        end
    | _ ->
        EField (e', f)

  (* Four different compilation schemes for inductives, in one pass. *)

  method! visit_ECons (_, typ) cons args =
    let lid =
      match typ with
      | TQualified lid -> lid
      | _ -> Warn.fatal_error "not an lid: %s: %a" cons ptyp typ
    in
    match Hashtbl.find map lid with
    | exception Not_found ->
        ECons (cons, List.map (self#visit_expr_w ()) args)
    | Eliminate _ ->
        (KList.one (List.map (self#visit_expr_w ()) args)).node
    | ToTaggedUnion _ ->
        ECons (cons, List.map (self#visit_expr_w ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        EEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        EFlat (List.map2 (fun n e -> Some n, self#visit_expr_w () e) names args)
    | ToFlatTaggedUnion branches ->
        let t_tag = TQualified (self#allocate_enum_lid lid branches) in
        let fields =
          if List.length args = 0 then
            []
          else
            let fields = snd (one_non_constant_branch branches) in
            List.map2 (fun (f, _) e -> Some f, self#visit_expr_w () e) fields args
        in
        EFlat ([
          Some field_for_tag, with_type t_tag (EEnum (mk_tag_lid lid cons))
        ] @ fields)

  method! visit_PCons (_, typ) cons args =
    let lid =
      match typ with
      | TQualified lid -> lid
      | _ -> Warn.fatal_error "not an lid: %s: %a" cons ptyp typ
    in
    match Hashtbl.find map lid with
    | exception Not_found ->
        PCons (cons, List.map (self#visit_pattern_w ()) args)
    | Eliminate _ ->
        (KList.one (List.map (self#visit_pattern_w ()) args)).node
    | ToTaggedUnion _ ->
        PCons (cons, List.map (self#visit_pattern_w ()) args)
    | ToEnum ->
        assert (List.length args = 0);
        PEnum (mk_tag_lid lid cons)
    | ToFlat names ->
        PRecord (List.map2 (fun n e -> n, self#visit_pattern_w () e) names args)
    | ToFlatTaggedUnion branches ->
        let t_tag = mk_tag_lid lid cons in
        let fields =
          if List.length args = 0 then
            []
          else
            let fields = snd (one_non_constant_branch branches) in
            List.map2 (fun (f, _) e -> f, self#visit_pattern_w () e) fields args
        in
        PRecord ([
          field_for_tag, with_type (TQualified t_tag) (PEnum (mk_tag_lid lid cons))
        ] @ fields)

  method private allocate_enum_lid lid branches =
    let tags = List.map (fun (cons, _fields) -> mk_tag_lid lid cons) branches in
    (* Pre-allocate the named type for this type's tags. Has to be done
     * here so that the enum declaration is inserted in the right spot.
     * *)
    let preferred_lid = fst lid, snd lid ^ "_tags" in
    match allocate_tag enums preferred_lid tags with
    | Found tag_lid ->
        tag_lid
    | Fresh decl ->
        pending := decl :: !pending;
        preferred_lid

  method! visit_DType env lid flags n def =
    let def = self#visit_type_def env def in
    match def with
    | Variant branches ->
        assert (n = 0);
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            DType (lid, flags, 0, Variant branches)
        | Eliminate t ->
            DType (lid, flags, 0, Abbrev t)
        | ToTaggedUnion _ ->
            ignore (self#allocate_enum_lid lid branches);
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
        | ToFlatTaggedUnion branches ->
            ignore (self#allocate_enum_lid lid branches);
            (* First field for the tag, then flatly, the fields of the only one
             * non-constant constructor. *)
            let f_tag = field_for_tag, (TQualified (self#allocate_enum_lid lid branches), false) in
            let fields = snd (one_non_constant_branch branches) in
            let fields = List.map (fun (f, t) -> Some f, t) (f_tag :: fields) in
            DType (lid, flags, 0, Flat fields)
            end
    | Flat fields ->
        assert (n = 0);
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            DType (lid, flags, 0, Flat fields)
        | Eliminate t ->
            DType (lid, flags, 0, Abbrev t)
        | _ ->
            assert false
        end
    | _ ->
        DType (lid, flags, n, def)

  (* Need the type to be mapped *after* the expression, so that we can examine
   * the old type. Maybe this should be the default? *)
  method! visit_expr_w env x =
    let node = self#visit_expr' (env, x.typ) x.node in
    let typ = self#visit_typ env x.typ in
    { node; typ }

  method! visit_pattern_w env x =
    let node = self#visit_pattern' (env, x.typ) x.node in
    let typ = self#visit_typ env x.typ in
    { node; typ }

  method! visit_with_type f (env, _) x =
      let node = f (env, x.typ) x.node in
      let typ = self#visit_typ env x.typ in
      { node; typ }

  method! visit_TQualified _ lid =
    match Hashtbl.find map lid with
    | exception Not_found ->
        TQualified lid
    | Eliminate t ->
        t
    | _ ->
        TQualified lid

  method! visit_EMatch ((_, t) as env) e branches =
    let e = self#visit_expr_w () e in
    let branches = self#visit_branches env branches in
    match e.typ with
    | TQualified lid ->
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            (* This might be a record in the first place. *)
            try_mk_flat e t branches
        | ToTaggedUnion _ | ToFlat _ | ToFlatTaggedUnion _ | Eliminate _ ->
            try_mk_flat e t branches
        | ToEnum ->
            try_mk_switch e branches
        end
    | _ ->
        (* For switches on constants *)
        try_mk_switch e branches
end

(* Third step: whole-program transformation to remove unit fields. *)

(* New: remove pointers to unit. *)
let remove_unit_buffers = object (self)
  inherit [_] map as super

  method! visit_TBuf _ t b =
    match t with
    | TUnit (* | TAny *) ->
        TUnit
    | _ ->
        TBuf (t, b)

  (* t has been rewritten *)
  method! visit_EField (_, t) e1 f =
    match t with
    | TUnit (* | TAny *) ->
        EUnit
    | _ ->
        let e1 = self#visit_expr_w () e1 in
        EField (e1, f)

  method! visit_EBufCreate env l e1 e2 =
    match e1.typ with
    | TUnit (* | TAny *) ->
        EUnit
    | _ ->
        super#visit_EBufCreate env l e1 e2

  method! visit_EBufCreateL (_, t as env) l es =
    match t with
    | TBuf (TUnit (* | TAny *), _) ->
        EUnit
    | _ ->
        super#visit_EBufCreateL env l es

  method! visit_EBufRead env e1 e2 =
    match e1.typ with
    | TBuf ((TUnit (* | TAny *)), _) ->
        EUnit
    | _ ->
      super#visit_EBufRead env e1 e2

  method! visit_EBufWrite env e1 e2 e3 =
    match e1.typ with
    | TBuf ((TUnit (* | TAny *)), _) ->
        EUnit
    | _ ->
      super#visit_EBufWrite env e1 e2 e3

  method! visit_EBufSub env e1 e2 =
    match e1.typ with
    | TBuf ((TUnit (* | TAny *)), _) ->
        EUnit
    | _ ->
      super#visit_EBufSub env e1 e2

  method! visit_EBufBlit env e1 e2 e3 e4 e5 =
    match e1.typ with
    | TBuf ((TUnit (* | TAny *)), _) ->
        EUnit
    | _ ->
      super#visit_EBufBlit env e1 e2 e3 e4 e5

  method! visit_EBufFill env e1 e2 e3 =
    match e1.typ with
    | TBuf ((TUnit (* | TAny *)), _) ->
        EUnit
    | _ ->
      super#visit_EBufFill env e1 e2 e3

  method! visit_EBufFree env e1 =
    match e1.typ with
    | TBuf ((TUnit (* | TAny *)), _) ->
        EUnit
    | _ ->
      super#visit_EBufFree env e1

  method! visit_EApp env e1 es =
    match e1.node, es with
    | EQualified ([ "LowStar"; "BufferOps" ], s), { typ = TBuf (TUnit, _); _ } :: _ when
      KString.starts_with s "op_Bang_Star__" ||
      KString.starts_with s "op_Star_Equals__" ->
        EUnit
    | _ ->
        super#visit_EApp env e1 es

end

let remove_unit_fields = object (self)

  inherit [_] map

  val erasable_fields = Hashtbl.create 41
  val mutable atoms = []

  method private is_erasable = function
    | TUnit | TAny -> true
    | _ -> false

  method private default_value = function
    | TUnit -> EUnit
    | TAny -> EAny
    | _ -> assert false

  method! visit_DType _ lid flags n type_def =
    match type_def with
    | Variant branches ->
        DType (lid, flags, n, self#rewrite_variant lid branches)
    | Flat fields ->
        DType (lid, flags, n, Flat (self#rewrite_fields lid None fields))
    | _ ->
        DType (lid, flags, n, type_def)

  (* Modify type definitions so that fields of type unit and any are removed.
   * Remember in a table that they are removed. *)
  method private rewrite_variant lid branches =
    let branches =
      List.map (fun (cons, fields) ->
        cons, self#rewrite_fields lid (Some cons) fields
      ) branches
    in
    Variant branches

  method private rewrite_fields:
    'a. lident -> string option -> ('a * (typ * bool)) list -> ('a * (typ * bool)) list
  = fun lid cons fields ->
    KList.filter_mapi (fun i (f, (t, m)) ->
      if self#is_erasable t then begin
        Hashtbl.add erasable_fields (lid, cons, i) ();
        None
      end else
        Some (f, (t, m))
    ) fields

  (* As we're about to visit a pattern, we collect binders for now-defunct
   * fields, and replace them with default values in the corresponding branch. *)
  method! visit_branch _ (binders, pat, expr) =
    let binders, pat, expr = open_branch binders pat expr in
    let pat = self#visit_pattern_w () pat in
    let expr = self#visit_expr_w () expr in
    let binders = List.filter (fun b -> not (List.mem b.node.atom atoms)) binders in
    let pat, expr = close_branch binders pat expr in
    binders, pat, expr

  (* Catch references to pattern-bound variables whose underlying field is gone. *)
  method! visit_EOpen (_, t) name a =
    if List.mem a atoms then
      self#default_value t
    else
      EOpen (name, a)

  (* In a constructor pattern, remove sub-patterns over erased fields and
   * remember them. *)
  method! visit_PCons (_, t) cons pats =
    let pats = KList.filter_mapi (fun i p ->
      if Hashtbl.mem erasable_fields (assert_tlid t, Some cons, i) then begin
        begin match p.node with
        | POpen (_, a) ->
            atoms <- a :: atoms
        | _ ->
            ()
        end;
        None
      end else
        Some (self#visit_pattern_w () p)
    ) pats in
    PCons (cons, pats)

  method! visit_PRecord (_, t) pats =
    let pats = KList.filter_mapi (fun i (f, p) ->
      if Hashtbl.mem erasable_fields (assert_tlid t, None, i) then begin
        begin match p.node with
        | POpen (_, a) ->
            atoms <- a :: atoms
        | _ ->
            ()
        end;
        None
      end else
        Some (f, self#visit_pattern_w () p)
    ) pats in
    PRecord pats

  method! visit_EFlat (_, t) exprs =
    let seq = ref [] in
    let exprs = KList.filter_mapi (fun i (f, e) ->
      if Hashtbl.mem erasable_fields (assert_tlid t, None, i) then begin
        if not (is_value e) then
          seq := (if e.typ = TUnit then e else with_unit (EIgnore (self#visit_expr_w () e))) :: !seq;
        None
      end else
        Some (f, self#visit_expr_w () e)
    ) exprs in
    let e = EFlat exprs in
    if List.length !seq > 0 then
      ESequence (List.rev_append !seq [ (with_type t e) ])
    else
      e

  method! visit_ECons (_, t) cons exprs =
    let seq = ref [] in
    let exprs = KList.filter_mapi (fun i e ->
      if Hashtbl.mem erasable_fields (assert_tlid t, Some cons, i) then begin
        if not (is_value e) then
          seq := (if e.typ = TUnit then e else with_unit (EIgnore (self#visit_expr_w () e))) :: !seq;
        None
      end else
        Some (self#visit_expr_w () e)
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
  Helpers.is_uu name

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

  inherit [_] map

  method! visit_ELet (_, t) b e1 e2 =
    match open_binder b e2 with
    | b, { node = EMatch ({ node = EOpen (_, a); _ }, branches); _ } when
      is_special b.node.name && !(b.node.mark) = 1 &&
      Atom.equal a b.node.atom ->
        self#visit_EMatch ((), t) e1 branches
    | _ ->
        ELet (b, self#visit_expr_w () e1, self#visit_expr_w () e2)

  method! visit_EMatch env e branches =
    let e = self#visit_expr env e in
    match e.node, branches with
    | EUnit, [ [], { node = PUnit; _ }, body ] ->
        (* match () with () -> ... is routinely generated by F*'s extraction. *)
        (self#visit_expr_w () body).node
    | _, [ [], { node = PBool true; _ }, b1; [ v ], { node = PBound 0; _ }, b2 ] when !(v.node.mark) = 0 ->
        (* An if-then-else is generated as:
         *   match e with true -> ... | uu____???? -> ...
         * where uu____???? is unused. *)
        let b1 = self#visit_expr_w () b1 in
        let _, b2 = open_binder v b2 in
        let b2 = self#visit_expr_w () b2 in
        if is_trivially_true e then
          b1.node
        else if is_trivially_false e then
          b2.node
        else
          EIfThenElse (e, b1, b2)
    | _ ->
        EMatch (e, self#visit_branches env branches)

  method! visit_branch env (binders, pat, expr) =
    let _, binders, pat, expr = List.fold_left (fun (i, binders, pat, expr) b ->
      if !(b.node.mark) = 0 && is_special b.node.name then
        i, binders, DeBruijn.subst_p pwild i pat, DeBruijn.subst any i expr
      else
        i + 1, b :: binders, pat, expr
    ) (0, [], pat, expr) (List.rev binders) in
    binders, self#visit_pattern env pat, self#visit_expr env expr
end


(* Fourth step is the core of this module: translating data types definitions as
 * tagged unions, and compiling pattern matches. *)

let union_field_of_cons = (^) "case_"

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
        mk (EIfThenElse (cond, e, mk (EAbort (Some "unreachable (pattern matches are exhaustive in F*)"))))
    | (cond, e) :: bs ->
        mk (EIfThenElse (cond, e, fold_ite bs))
  in
  if is_simple_expression e_scrut then
    let name_scrut = e_scrut in
    let branches = List.map (compile_branch env name_scrut) branches in
    fold_ite branches
  else
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

  inherit [_] map

  method private tag_and_val_type lid branches =
    let tags = List.map (fun (cons, _fields) -> mk_tag_lid lid cons) branches in
    let structs = KList.filter_map (fun (cons, fields) ->
      let fields = List.map (fun (f, t) -> Some f, t) fields in
      match List.length fields with
      | 0 ->
          (* No arguments to this data constructor: no need to have a case in
           * the union. *)
          None
      | 1 ->
          (* One argument to the data constructor: this is the case itself. We
           * lose the pretty name. *)
          Some (union_field_of_cons cons, fst (snd (KList.one fields)))
      | _ ->
          (* Generic scheme: a struct for all the arguments of the data
           * constructor. *)
          Some (union_field_of_cons cons, TAnonymous (Flat fields))
    ) branches in
    let preferred_lid = fst lid, snd lid ^ "_tags" in
    let tag_lid =
      match allocate_tag enums preferred_lid tags with
      | Found lid -> lid
      | Fresh _ ->
          (* pre-allocated by the previous phase *)
          Warn.fatal_error "could not find tag lid for %a" plid preferred_lid
    in
    TQualified tag_lid, TAnonymous (Union structs)

  method! visit_DType _ lid flags n type_def =
    match type_def with
    | Variant branches ->
        DType (lid, flags, n, self#rewrite_variant lid branches)
    | _ ->
        DType (lid, flags, n, type_def)

  (* A variant declaration is a struct declaration with two fields:
   * - [field_for_tag] is the field that holds the "tag" whose type is an
   *   anonymous union
   * - [field_for_union] is the field that holds the actual value determined by
   *   the tag; it is the union of several struct types, one for each
   *   constructor. *)
  method private rewrite_variant lid branches =
    let t_tag, t_val = self#tag_and_val_type lid branches in
    Flat [
      Some field_for_tag, (t_tag, false);
      Some field_for_union, (t_val, false)
    ]

  (* A pattern on a constructor becomes a pattern on a struct and one of its
   * union fields. *)
  method! visit_PCons (_, t) cons fields =
    let lid = assert_tlid t in
    let branches = assert_branches map lid in
    let field_names = field_names_of_cons cons branches in
    let fields = List.map (self#visit_pattern_w ()) fields in
    let record_pat = PRecord (List.combine field_names fields) in
    let t_tag, t_val = self#tag_and_val_type lid branches in
    (** This is sound because we rely on left-to-right, lazy semantics for
     * pattern-matching. So, we read the "right" field from the union only
     * after we've ascertained that we're in the right case. *)
    PRecord ([ field_for_tag, with_type t_tag (PEnum (mk_tag_lid lid cons)) ] @
    match List.length fields with
    | 0 ->
        []
    | 1 ->
        [ field_for_union, with_type t_val (PRecord [
          union_field_of_cons cons, KList.one fields
        ])]
    | _ ->
        [ field_for_union, with_type t_val (PRecord [
          union_field_of_cons cons, with_type TAny record_pat
        ])])

  method! visit_ECons (_, t) cons exprs =
    let lid = assert_tlid t in
    let branches = assert_branches map lid in
    let field_names = field_names_of_cons cons branches in
    let field_names = List.map (fun x -> Some x) field_names in
    let exprs = List.map (self#visit_expr_w ()) exprs in
    let record_expr = EFlat (List.combine field_names exprs) in
    let t_tag, t_val = self#tag_and_val_type lid branches in
    EFlat (
      [ Some field_for_tag, with_type t_tag (EEnum (mk_tag_lid lid cons)) ] @
      match List.length exprs with
      | 0 ->
          []
      | 1 ->
          [ Some field_for_union, with_type t_val (
            EFlat [ Some (union_field_of_cons cons), KList.one exprs])]
      | _ ->
          [ Some field_for_union, with_type t_val (
              EFlat [ Some (union_field_of_cons cons), with_type TAny record_expr ])]
    )

  (* The match transformation is tricky: we open all binders. *)
  method! visit_DFunction env cc flags n ret name binders expr =
    let binders, expr = open_binders binders expr in
    let expr = self#visit_expr_w env expr in
    let expr = close_binders binders expr in
    DFunction (cc, flags, n, ret, name, binders, expr)

  method! visit_ELet _ binder e1 e2 =
    let e1 = self#visit_expr_w () e1 in
    let binder, e2 = open_binder binder e2 in
    let e2 = self#visit_expr_w () e2 in
    let e2 = close_binder binder e2 in
    ELet (binder, e1, e2)

  method! visit_branches _ branches =
    List.map (fun (binders, pat, expr) ->
      (* Not opening the branch... since we don't have binders inside of
       * patterns. *)
      let binders, expr = open_binders binders expr in
      let pat = self#visit_pattern_w () pat in
      let expr = self#visit_expr_w () expr in
      let expr = close_binders binders expr in
      binders, pat, expr
    ) branches

  (* Then compile patterns for those matches whose scrutinee is a data type.
   * Other matches remain (e.g. on units and booleans... [Helpers] will take
   * care of those dummy matches. *)
  method visit_EMatch env e_scrut branches =
    let e_scrut = self#visit_expr env e_scrut in
    let branches = self#visit_branches env branches in
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
  inherit [_] map as super

  method! visit_EField env e f =
    match e.typ with
    | TQualified lid when f = field_for_union && is_tagged_union map lid ->
        let e = self#visit_expr env e in
        e.node
    | _ ->
        EField (self#visit_expr env e, f)

  method! visit_decl env d =
    match d with
    | DType (lid, flags, 0, Flat [ Some f1, t1; Some f2, t2 ]) when
      f1 = field_for_tag && f2 = field_for_union &&
      is_tagged_union map lid ->
        DType (lid, flags, 0, Flat [ Some f1, t1; None, t2 ])
    | _ ->
        super#visit_decl env d

  method! visit_EFlat (env, t) fields =
    match fields, t with
    | [ Some f1, t1; Some f2, t2 ], TQualified lid when
      f1 = field_for_tag && f2 = field_for_union &&
      is_tagged_union map lid ->
        EFlat [ Some f1, t1; None, t2 ]
    | _ ->
        EFlat (self#visit_fields_e_opt_w env fields)

end

let debug_map map =
  Hashtbl.iter (fun lid scheme ->
    KPrint.bprintf "%a goes to %s\n" plid lid (
      match scheme with
      | Eliminate _ -> "eliminate"
      | ToEnum -> "enum"
      | ToFlat _ -> "flat"
      | ToTaggedUnion _ -> "tagged union"
      | ToFlatTaggedUnion _ -> "flat tagged union"
    )
  ) map


(* Seventh step: remove casts to struct types ... not supported by the C
 * compiler. *)
let remove_non_scalar_casts = object (self)
  inherit [_] map

  method! visit_ECast (env, t) e t_dest =
    let e = self#visit_expr_w env e in
    match t_dest with
    | TQualified lid ->
        (* Type abbreviations have been inlined at this stage. If an lid
         * remains, it's a scalar type. *)
        begin match t with
        | TQualified lid' when lid <> lid' ->
            KPrint.bprintf "non-scalar cast from %a to %a -- please send test \
              case to Jonathan, thanks\n" ptyp t ptyp t_dest
        | _ ->
            ()
        end;
        e.node
    | _ ->
        ECast (e, t_dest)

end

(* An early step: remove "full" matches, i.e. those that don't necessitate
 * the evaluation of a temporary scrutinee and can be compiled into a series of
 * nested, plain let-bindings. Note that we do a local, manual commutation of
 * let/match, since simplify2 has not run yet.
 *
 * Generic rewriting rule of the form:
 *   (i)   match (e1, e2) with (x, y) -> e  ~~~>
 *         let x = e1 in let y = e2 in e
 * Specific rewriting rule:
 *   (ii)  match let x = e0 in (e1, e2) with (x, y) -> e  ~~~>
 *         let x = e0 in match (e1, e2) with (x, y) -> e
 *)
let remove_full_matches = object (self)

  inherit [_] map as super

  method! visit_EMatch (_, t as env) scrut branches =
    let scrut0 = scrut in
    let scrut = self#visit_expr env scrut in
    match scrut.node with
    | ELet (b, e1, e2) ->
        let b, e2 = open_binder b e2 in
        (self#visit_expr env (with_type t (ELet (b, e1,
          close_binder b (with_type t (EMatch (e2, branches))))))).node
    | _ ->
        let rec explode pat scrut =
          match pat.node, scrut.node with
          | POpen (_, a), _ ->
              [ a, scrut ]
          | PTuple ps, ETuple es ->
              List.flatten (List.map2 explode ps es)
          | PRecord fieldpats, EFlat fieldexprs ->
              List.flatten (List.map2 (fun (f, p) (f', e) ->
                assert (Some f = f');
                explode p e
              ) fieldpats fieldexprs)
          | PCons (cons, ps), ECons (cons', es) ->
              if cons = cons' then
                List.flatten (List.map2 explode ps es)
              else
                (* This indicates unreachable code; see test/Mini.fst *)
                raise Not_found
          | _ ->
              (* Todo: records *)
              raise Not_found
        in
        match branches with
        | [ binders, pat, e ] ->
            begin try
              let e = self#visit_expr env e in
              let binders, pat, e = open_branch binders pat e in
              let pairs = explode pat scrut in
              let binders = List.map (fun b -> b, List.assoc b.node.atom pairs) binders in
              (Helpers.nest binders t e).node
            with Not_found ->
              super#visit_EMatch env scrut0 branches
            end
        | _ ->
            super#visit_EMatch env scrut branches
end

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)
(* debug_map (fst map); *)

let simplify files =
  let files = remove_trivial_matches#visit_files () files in
  let files = remove_full_matches#visit_files () files in
  files

let everything files =
  let files = remove_unit_buffers#visit_files () files in
  let files = remove_unit_fields#visit_files () files in
  let map = build_scheme_map files in
  let files = (compile_simple_matches map)#visit_files () files in
  let files = (compile_all_matches map)#visit_files () files in
  let files = remove_non_scalar_casts#visit_files () files in
  map, files

let anonymous_unions map files =
  (anonymous_unions map)#visit_files () files
