(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(* Monomorphization of functions and data types. *)

open Ast
open PrintAst.Ops
open Helpers

module K = Constant

(* Monomorphization of data type definitions **********************************)

(* A whole-program map from type lids to their definitions. *)
let build_def_map files =
  build_map files (fun map -> function
    | DType (lid, flags, _, def) ->
        Hashtbl.add map lid (flags, def)
    | _ ->
        ()
  )

(* A set of hints to pick better names for monomorphized data types. Filled by
 * Inlining.ml. *)
let hints: ((lident * typ list) * lident) list ref = ref []

let debug_hints () =
  KPrint.bprintf "==== state of naming hints ====\n";
  List.iter (fun ((hd, args), lid) ->
    KPrint.bprintf "%a --> %a\n" ptyp (TApp (hd, args)) plid lid
  ) !hints


(* We visit type declarations in order to monomorphize parameterized type
 * declarations and insert forward declarations as needed. Consider, for
 * instance:
 *
 *   type linked_list = Nil | Cons of int * buffer linked_list
 *
 * We see this phase as a classic graph traversal where the nodes are pairs of
 * types and effective type arguments, and the edges are uses. The example above
 * is visited, then a forward declaration is inserted to break the cycle from
 * the node (linked_list, []) to itself. This gives:
 *
 *   type linked_list // a forward declaration
 *   type linked_list = Nil | Cons of int * buffer linked_list
 *
 * This will be turned into the following C code:
 *
 *   struct s;
 *   typedef struct s t;
 *   typedef struct s {
 *     int x;
 *     t *next;
 *   } t;
 *
 * We visit non-parameterized type declarations at declaration site.
 * However, parameterized declarations, such as the following, are visited at
 * use-site:
 *
 *   type linked_list a = | Nil | Cons: x:int -> buffer (linked_list a)
 *
 * This gives:
 *
 *   type linked_list_int;
 *   type linked_list_int = Nil | Cons of int * buffer linked_list_int
 *)
type node = lident * typ list
type color = Gray | Black
let tuple_lid = [ "K" ], ""

let monomorphize_data_types map = object(self)

  inherit [_] map as super

  (* Assigning a color to each node. *)
  val state = Hashtbl.create 41
  (* We view tuples as the application of a special lid to its arguments. *)
  (* We record pending declarations as we visit top-level declarations. *)
  val mutable pending = []
  (* Current file, for warning purposes. *)
  val mutable current_file = ""

  (* Record a new declaration. *)
  method private record (d: decl) =
    if Drop.file current_file then
      Warn.(maybe_fatal_error ("", DropDeclaration (lid_of_decl d, current_file)));
    pending <- d :: pending

  (* Clear all the pending declarations. *)
  method private clear () =
    let r = List.rev pending in
    pending <- [];
    r

  (* Compute the name of a given node in the graph. *)
  method private lid_of (n: node) =
    let lid, args = n in
    if List.length args > 0 then
      try
        let pretty = List.assoc n !hints in
        if Options.debug "names" then
          KPrint.bprintf "Hit: %a --> %a\n" ptyp (TApp (lid, args)) plid pretty;
        pretty
      with Not_found ->
        if Options.debug "names" then begin
          KPrint.bprintf "No hit: %a\n" ptyp (TApp (lid, args));
          debug_hints ()
        end;
        let doc = PPrint.(separate_map underscore PrintAst.print_typ args) in
        fst lid, KPrint.bsprintf "%s__%a" (snd lid) PrintCommon.pdoc doc
    else
      lid

  (* Prettifying the field names for n-uples. *)
  method private field_at i =
    match i with
    | 0 -> "fst"
    | 1 -> "snd"
    | 2 -> "thd"
    | _ -> Printf.sprintf "f%d" i

  (* Visit a given node in the graph, modifying [pending] to append in reverse
   * order declarations as they are needed, including that of the node we are
   * visiting. *)
  method private visit_node (n: node) =
    let lid, args = n in
    (* White, gray or black? *)
    begin match Hashtbl.find state n with
    | exception Not_found ->
        (* Update hints table to now use names that have been previously
         * allocated, including the current node's (in case this is a
         * recursive type). Cannot use the current visitor because it would
         * force visiting sub-nodes that we don't intend to visit yet. *)
        hints := List.map (fun ((hd, args), lid) ->
          (hd, List.map (
            (object
              inherit [_] map as self'

              method! visit_TApp _ hd args =
                if Hashtbl.mem state (hd, args) then
                  let args = List.map (self'#visit_typ ()) args in
                  TQualified (self#lid_of (hd, args))
                else
                  let args = List.map (self'#visit_typ ()) args in
                  TApp (hd, args)

              method! visit_TTuple _ args =
                if Hashtbl.mem state (tuple_lid, args) then
                  let args = List.map (self'#visit_typ ()) args in
                  TQualified (self#lid_of (tuple_lid, args))
                else
                  let args = List.map (self'#visit_typ ()) args in
                  TTuple args
            end)#visit_typ ()
          ) args), lid) !hints;

        (* Subtletly: we decline to insert type monomorphizations in dropped
         * files, on the basis that they might be needed later in an actual
         * file. *)
        if lid = tuple_lid then
          (* For tuples, we immediately know how to generate a definition. *)
          let fields = List.mapi (fun i arg -> Some (self#field_at i), (arg, false)) args in
          self#record (DType (self#lid_of n, [ Common.Private ], 0, Flat fields));
          Hashtbl.add state n Black
        else begin
          (* This specific node has not been visited yet. *)
          Hashtbl.add state n Gray;

          let subst fields = List.map (fun (field, (t, m)) ->
            field, (DeBruijn.subst_tn args t, m)
          ) fields in
          begin match Hashtbl.find map lid with
          | exception Not_found ->
              ()
          | flags, Variant branches ->
              let branches = List.map (fun (cons, fields) -> cons, subst fields) branches in
              let branches = self#visit_branches_t () branches in
              self#record (DType (self#lid_of n, flags, 0, Variant branches))
          | flags, Flat fields ->
              let fields = self#visit_fields_t_opt () (subst fields) in
              self#record (DType (self#lid_of n, flags, 0, Flat fields))
          | flags, Abbrev t ->
              let t = DeBruijn.subst_tn args t in
              let t = self#visit_typ () t in
              self#record (DType (self#lid_of n, flags, 0, Abbrev t))
          | _ ->
              ()
          end;
          Hashtbl.replace state n Black
        end
    | Gray ->
        begin match Hashtbl.find map lid with
        | exception Not_found ->
            ()
        | flags, _ ->
            self#record (DType (self#lid_of n, flags, 0, Forward))
        end
    | Black ->
        ()
    end;
    self#lid_of n

  (* Top-level, non-parameterized declarations are root of our graph traversal.
   * This also visits, via occurrences in code, applications of parameterized
   * types. *)
  method! visit_file _ file =
    let name, decls = file in
    current_file <- name;
    name, KList.map_flatten (fun d ->
      match d with
      | DType (lid, _, n, (Flat _ | Variant _ | Abbrev _)) ->
          ignore (self#visit_decl () d);
          if n = 0 then
            ignore (self#visit_node (lid, []));
          self#clear ()

      | _ ->
          self#clear () @ [ self#visit_decl () d ]
    ) decls

  method! visit_DType env name flags n d =
    if n > 0 then
      (* This drops polymorphic type definitions by making them a no-op that
       * registers nothing. *)
      DType (name, flags, n, d)
    else
      super#visit_DType env name flags n d

  method! visit_ETuple _ es =
    EFlat (List.mapi (fun i e -> Some (self#field_at i), self#visit_expr_w () e) es)

  method! visit_PTuple _ pats =
    PRecord (List.mapi (fun i p -> self#field_at i, self#visit_pattern_w () p) pats)

  method! visit_TTuple _ ts =
    TQualified (self#visit_node (tuple_lid, List.map (self#visit_typ ()) ts))

  method! visit_TQualified _ lid =
    TQualified (self#visit_node (lid, []))

  method! visit_TApp _ lid ts =
    TQualified (self#visit_node (lid, List.map (self#visit_typ ()) ts))
end

let datatypes files =
  let map = build_def_map files in
  (monomorphize_data_types map)#visit_files () files


(* Type monomorphization of functions. ****************************************)

(* JP: TODO: share the functionality with type monomorphization... the call to
 * Hashtbl.find is in the visitor but the Gen functionality is clearly
 * outside... sigh. *)
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

  let register_def current_file original_lid ts lid def =
    Hashtbl.add generated_lids (original_lid, ts) lid;
    let d = def () in
    if Drop.file current_file then
      Warn.(maybe_fatal_error ("", DropDeclaration (lid_of_decl d, current_file)));
    pending_defs := d :: !pending_defs;
    lid

  let clear () =
    let r = List.rev !pending_defs in
    pending_defs := [];
    r
end


(* This follows the same structure as for data types, with a whole-program from
 * function & global lids to their respective definitions. Every type
 * application (caught via the visitor) generates an instance. *)
let functions files =
  let map = Helpers.build_map files (fun map -> function
    | DFunction (cc, flags, n, t, name, b, body) ->
        if n > 0 then
          Hashtbl.add map name (`Function (cc, flags, n, t, name, b, body))
    | DGlobal (flags, name, n, t, body) ->
        if n > 0 then
          Hashtbl.add map name (`Global (flags, name, n, t, body))
    | _ ->
        ()
  ) in

  let monomorphize = object(self)

    inherit [_] map

    (* Current file, for warning purposes. *)
    val mutable current_file = ""

    method! visit_file _ file =
      let file_name, decls = file in
      current_file <- file_name;
      file_name, KList.map_flatten (function
        | DFunction (cc, flags, n, ret, name, binders, body) ->
            if Hashtbl.mem map name then
              []
            else
              let d = DFunction (cc, flags, n, ret, name, binders, self#visit_expr_w () body) in
              assert (n = 0);
              Gen.clear () @ [ d ]
        | DGlobal (flags, name, n, t, body) ->
            if Hashtbl.mem map name then
              []
            else
              let d = DGlobal (flags, name, n, t, self#visit_expr_w () body) in
              assert (n = 0);
              Gen.clear () @ [ d ]
        | d ->
            [ d ]
      ) decls

    method! visit_ETApp env e ts =
      match e.node with
      | EQualified lid ->
          begin try
            (* Already monomorphized? *)
            EQualified (Hashtbl.find Gen.generated_lids (lid, ts))
          with Not_found ->
            match Hashtbl.find map lid with
            | exception Not_found ->
                (* External function. Bail. *)
                (self#visit_expr env e).node
            | `Function (cc, flags, n, ret, name, binders, body) ->
                (* Need to generate a new instance. *)
                if n <> List.length ts then begin
                  KPrint.bprintf "%a is not fully type-applied!\n" plid lid;
                  (self#visit_expr env e).node
                end else
                  (* The thunk allows registering the name before visiting the
                   * body, for polymorphic recursive functions. *)
                  let name = Gen.gen_lid name ts in
                  let def () =
                    let ret = DeBruijn.subst_tn ts ret in
                    let binders = List.map (fun { node; typ } ->
                      { node; typ = DeBruijn.subst_tn ts typ }
                    ) binders in
                    let body = DeBruijn.subst_ten ts body in
                    let body = self#visit_expr env body in
                    DFunction (cc, flags, 0, ret, name, binders, body)
                  in
                  EQualified (Gen.register_def current_file lid ts name def)

            | `Global (flags, name, n, t, body) ->
                if n <> List.length ts then begin
                  KPrint.bprintf "%a is not fully type-applied!\n" plid lid;
                  (self#visit_expr env e).node
                end else
                  let name = Gen.gen_lid name ts in
                  let def () =
                    let t = DeBruijn.subst_tn ts t in
                    let body = DeBruijn.subst_ten ts body in
                    let body = self#visit_expr env body in
                    DGlobal (flags, name, 0, t, body)
                  in
                  EQualified (Gen.register_def current_file lid ts name def)

          end

      | EOp ((K.Eq | K.Neq), _) ->
          ETApp (e, ts)

      | EOp (_, _) ->
         (self#visit_expr env e).node

      | _ ->
          KPrint.bprintf "%a is not an lid in the type application\n" pexpr e;
          (self#visit_expr env e).node

  end in

  monomorphize#visit_files () files


let equalities files =

  let types_map = Helpers.build_map files (fun map d ->
    match d with
    | DType (lid, _, _, d) -> Hashtbl.add map lid d
    | _ -> ()
  ) in

  let monomorphize = object(self)

    inherit [_] map as super

    val mutable current_file = ""
    val mutable has_cycle = false

    method! visit_file env file =
      let file_name, decls = file in
      current_file <- file_name;
      file_name, KList.map_flatten (fun d ->
        let d = self#visit_decl env d in
        let equalities = Gen.clear () in
        let equalities = List.map (function
          | DFunction (cc, flags, n, ret, name, binders, body) ->
              (* This is a highly conservative criterion that is triggered by
               * any recursive type; we could be smarter and only break the
               * cycles by marking ONE declaration public.  *)
              let flags =
                if has_cycle then
                  List.filter ((<>) Common.Private) flags
                else
                  flags
              in
              DFunction (cc, flags, n, ret, name, binders, body)
          | d ->
              d
        ) equalities in
        has_cycle <- false;
        equalities @ [ d ]
      ) decls

    (* For type [t] and either [op = Eq] or [op = Neq], generate a recursive
     * equality predicate that implements F*'s structural equality. *)
    method private generate_equality t op =
      (* A set of helpers use for generating abstract syntax. *)
      let eq_kind, eq_lid = match op with
        | K.Eq -> `Eq, ([], "__eq")
        | K.Neq -> `Neq, ([], "__neq")
        | _ -> assert false
      in
      let eq_typ = TArrow (t, TArrow (t, TBool)) in
      let instance_lid = Gen.gen_lid eq_lid [ t ] in
      let x = fresh_binder "x" t in
      let y = fresh_binder "y" t in

      match t with
      | TQualified ([ "Prims" ], ("int" | "nat" | "pos")) ->
          EOp (op, K.CInt)

      | TInt w ->
          EOp (op, w)

      | TBool ->
          EOp (op, K.Bool)

      | TBuf _ ->
          (* Buffers do not have eqtype. The only instance of pointer types compared via equality is
           * thus references, which are compared by address. Type-checking is lax and will accept
           * this even though the K.Bool is incorrect... *)
          EOp (op, K.UInt64)

      | TQualified lid when Hashtbl.mem types_map lid ->
          begin try
            (* Already monomorphized? *)
            let existing_lid = Hashtbl.find Gen.generated_lids (eq_lid, [ t ]) in
            let is_cycle = List.exists (fun d -> lid_of_decl d = existing_lid) !Gen.pending_defs in
            if is_cycle then
              has_cycle <- true;
            EQualified existing_lid
          with Not_found ->
            let mk_conj_or_disj es =
              match eq_kind with
              | `Eq -> List.fold_left mk_and etrue es
              | `Neq -> List.fold_left mk_or efalse es
            in
            let mk_rec_equality t e1 e2 =
              match t with
              | TUnit ->
                  (* This phase occurs after monomorphization, but before the
                   * elimination of unit arguments to data constructors. (Could
                   * we move it to occur after that? Unclear.) As such, we are
                   * sometimes tasked we generating recursive equality
                   * predicates for units. [generate_equality] can only return a
                   * function, so we intercept the recursive call here, and
                   * insert "true" for units, rather than going through the
                   * fallback that generates an "extern" call. *)
                  with_type TBool (EBool true)
              | _ ->
                  with_type TBool (
                    EApp (
                      with_type (TArrow (t, TArrow (t, TBool))) (
                        self#generate_equality t op), [
                        with_type t e1;
                        with_type t e2]))
            in
            match Hashtbl.find types_map lid with
            | Abbrev _ | Enum _ | Union _ | Forward ->
                (* No abbreviations (this runs after inline_type abbrevs).
                 * No Enum / Union / Forward (this runs before data types). *)
                assert false
            | Flat fields ->
                (* Either a conjunction of equalities, or a disjunction of inequalities. *)
                let def () =
                  let sub_equalities = List.map (fun (f, (t_field, _)) ->
                    let f = Option.must f in
                    (* __eq__ x.f y.f *)
                    mk_rec_equality t_field
                      (EField (with_type t (EBound 0), f))
                      (EField (with_type t (EBound 1), f))
                  ) fields in
                  DFunction (None, [ Common.Private ], 0, TBool, instance_lid, [ y; x ],
                    mk_conj_or_disj sub_equalities)
                in
                EQualified (Gen.register_def current_file eq_lid [ t ] instance_lid def)
            | Variant branches ->
                let def () =
                  let fail_case = match eq_kind with
                    | `Eq -> efalse
                    | `Neq -> etrue
                  in
                  (* let __eq__typ y x = *)
                  DFunction (None, [ Common.Private ], 0, TBool, instance_lid, [ y; x ],
                    (* match *)
                    with_type TBool (EMatch (
                      (* x with *)
                      with_type t (EBound 0),
                      List.map (fun (cons, fields) ->
                        let n = List.length fields in
                        let binders_x = List.map (fun (f, (t, _)) ->
                          fresh_binder (KPrint.bsprintf "x_%s" f) t
                        ) fields in
                        (* \. xn ... x0. *)
                        List.rev binders_x, 
                        (* A x0 ... xn -> *)
                        with_type t (PCons (cons, List.mapi (fun i (_, (t_f, _)) ->
                          with_type t_f (PBound i)) fields)),
                        (* match *)
                        with_type TBool (EMatch (
                          (* y with *)
                          with_type t (EBound (n + 1)),
                          let binders_y = List.map (fun (f, (t, _)) ->
                            fresh_binder (KPrint.bsprintf "y_%s" f) t
                          ) fields in
                          [
                            (* \. yn ... y0 *)
                            List.rev binders_y,
                            (* A y0 ... yn -> *)
                            with_type t (PCons (cons, List.mapi (fun i (_, (t_f, _)) ->
                              with_type t_f (PBound i)) fields)),
                            (* ___eq___ xi yi *)
                            mk_conj_or_disj (List.mapi (fun i (_, (t, _)) ->
                              mk_rec_equality t (EBound i) (EBound (n + i))
                            ) fields);
                            (* _ -> false *)
                            [],
                            with_type t PWild,
                            fail_case
                      ]))) branches @ [
                        (* _ -> false *)
                        [],
                        with_type t PWild,
                        fail_case
                      ]))) in
                EQualified (Gen.register_def current_file eq_lid [ t ] instance_lid def)
          end

      | _ ->
          try
            (* Already monomorphized? *)
            EQualified (Hashtbl.find Gen.generated_lids (eq_lid, [ t ]))
          with Not_found ->
            (* External type without a definition. Comparison of function types? *)
            begin match eq_kind with
            | `Neq ->
                (* let __neq__t x y = not (__eq__t x y) *)
                let def () =
                  let body = mk_not (with_type TBool (
                    EApp (with_type eq_typ (self#generate_equality t K.Eq), [
                      with_type t (EBound 0); with_type t (EBound 1) ])))
                  in
                  DFunction (None, [], 0, TBool, instance_lid, [ y; x ], body)
                in
                EQualified (Gen.register_def current_file eq_lid [ t ] instance_lid def)
            | `Eq ->
                (* assume val __eq__t: t -> t -> bool *)
                let def () = DExternal (None, [], instance_lid, eq_typ, [ "x"; "y" ]) in
                EQualified (Gen.register_def current_file eq_lid [ t ] instance_lid def)
            end

    method! visit_ETApp _ e ts =
      match e.node with
      | EOp (K.Eq | K.Neq as op, _) ->
          let t = KList.one ts in
          self#generate_equality t op
      | _ ->
          failwith "should've been eliminated by Monomorphize.functions"

    (* New feature: generate top-level specialized equalities in case a
     * higher-order occurrence of the equality operator occurs, at a scalar
     * type. *)

    method private eta_expand_op op w =
      let eq_lid = match op with
        | K.Eq -> [], "__eq"
        | K.Neq -> [], "__neq"
        | _ -> assert false
      in
      let t = TInt w in
      try
        (* Already monomorphized? *)
        let existing_lid = Hashtbl.find Gen.generated_lids (eq_lid, [ t ]) in
        EQualified existing_lid
      with Not_found ->
        let eq_typ = TArrow (t, TArrow (t, TBool)) in
        let instance_lid = Gen.gen_lid eq_lid [ t ] in
        let x = fresh_binder "x" t in
        let y = fresh_binder "y" t in
        EQualified (Gen.register_def current_file eq_lid [ TInt w ] instance_lid (fun _ ->
          DFunction (None, [ Common.Private ], 0, TBool, instance_lid, [ y; x ],
            with_type TBool (
              EApp (with_type eq_typ (EOp (op, w)), [
                with_type t (EBound 0); with_type t (EBound 1) ])))))

    method! visit_EApp env e es =
      match e.node with
      | EOp ((K.Eq | K.Neq), _) -> EApp (e, List.map (self#visit_expr env) es)
      | _ -> super#visit_EApp env e es

    method! visit_EOp _ op w =
      match op with
      | K.Eq | K.Neq ->
          (* If we get here, then this is an unapplied equality appearing in an
           * expression, which then needs to be hoisted into an eta-expanded
           * top-level definition. Note that we will still bail on partial
           * applications of the equality. *)
          self#eta_expand_op op w
      | _ ->
          EOp (op, w)

  end in

  monomorphize#visit_files () files
