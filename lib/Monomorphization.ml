(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(* Monomorphization of functions and data types. *)

open Ast
open PrintAst.Ops
open Helpers

module K = Constant

(* Name generation ***********************************************************)

(* This module encapsulates the name generation facility that to each monomorphized type or
   function, associates a suitable top-level name. Specifically, given a polymorphic `lid` and
   concrete type arguments `ts` and expression arguments `cgs`, this module picks a name and records
   that information in a global state. *)

let explanation = {|Some debug info to figure out what the hash codes correspond to...

"trait impl" means that the charon-provided name includes the name of the trait
implementation block that this function was defined in -- this is typically a
rather long name, so here we simply feed the string through a hash function to
compute a unique two-byte code that allows shortening the function name
(otherwise, the C code would be pretty unreadable)

the other case is for parameterized types and functions
- for types, we need to monomorphize a type according to the choice of type and
  const generic arguments; to avoid a long name, we simply feed those arguments
  into a hash function and take a two-byte unique suffix
- for functions, we need to monomorphize the function according to the choice of
  type, const generic arguments, and the choice of trait implementation (which
  internally amounts to passing a function pointer for each one of the
  implementation methods in the chosen trait); those are also fed into the hash
  function to compute a two-byte unique suffix

because of this, the suffixes are identical if, say, two functions rely on the
same set of monomorphization parameters, or originate from the same trait impl

--------------------------------------------------------------------------------

|}


let maybe_debug_hash =
  let oc = ref None in
  let seen = Hashtbl.create 41 in
  let printed_info = ref false in
  let open_out () =
    match !oc with
    | Some oc -> oc
    | None -> let s = open_out_bin "hash_map" in oc := Some s; s
  in
  fun hash pretty ->
    if Options.debug "hashes" && not (Hashtbl.mem seen hash) then begin
      if not !printed_info then
        output_string (open_out ()) explanation;
      printed_info := true;
      KPrint.bfprintf (open_out ()) "%02x --> %a\n\n"
        (hash land 0xFF)
        PrintCommon.pdoc (Lazy.force pretty);
      Hashtbl.add seen hash ()
    end

module NameGen = struct

  open PPrint
  open PrintAst

  (* TODO: expose via an option if there is enough interest *)
  let short_names = ref false

  (* This avoids collisions, and puts monomorphized types and functions within the same namespace --
     this could potentially generate spurious collisions, though I doubt this is likely (famous last
     words?). *)
  let seen = Hashtbl.create 41

  (* For types, the arguments at application site are `cg`s, and we do not have names available
     (this might be worth fixing).
     For expressions, the arguments at application site are `expr`s; all of the arguments go into
     hash-consing, but for pretty-printing, we only retain those that are const generics, not those
     that are trait instance methods. *)
  type extra = Cg of cg list | Expr of int * expr list * binder_w list

  let print_extra = function
    | Cg cgs -> separate_map underscore print_cg cgs
    | Expr (n_cgs, cgs, _) -> separate_map underscore (print_expr empty_env) (fst (KList.split n_cgs cgs))

  (* An informative comment in case the short name option is chosen. *)
  let gen_comment original_name ts extra =
    let pconst e =
      match e.node with
      | EConstant (_, s) -> string s
      | _ -> failwith "impossible"
    in
    let extra = match extra with
      | Cg cgs ->
          if cgs <> [] then
            string "with const generics" ^^ break 1 ^^ hardline ^^
            separate_map hardline (fun cg -> string "-" ^^ space ^^ print_cg cg) cgs
          else
            empty
      | Expr (n_cgs, cgs, binders) ->
          if cgs <> [] then
            let cgs, _ = KList.split n_cgs cgs in
            let binders, _ = KList.split n_cgs binders in
            string "with const generics" ^^ break 1 ^^ hardline ^^
            separate_map hardline (fun (b, e) -> string "-" ^^ space ^^ string b.node.name ^^ equals ^^
            space ^^ pconst e) (List.combine binders cgs)
          else
            empty
    in
    let comment =
      string "A monomorphic instance of " ^^ print_lidents [ original_name ] ^^ hardline ^^
      (if ts <> [] then string "with types" ^^ break 1 ^^ group (print_typs ts) ^^ hardline else
        empty) ^^
      extra
    in
    Common.Comment (KPrint.bsprintf "%a" PrintCommon.pdoc comment)

  let distinguished: (MonomorphizationState.node * lident) list ref = ref []

  let gen_lid lid ts (extra: extra) =
    if !short_names then
      if lid = tuple_lid && List.for_all ((=) (List.hd ts)) ts then
        let n = KPrint.bsprintf "%a_x%d" ptyp (List.hd ts) (List.length ts) in
        ([], n), [ Common.AutoGenerated ]
      else
        let m, n = if lid = tuple_lid then [], "tuple" else lid in
        (* Skip binders that are there for debugging only. *)
        let hash = match extra with
          | Cg cgs -> Hashtbl.hash (ts, cgs)
          | Expr (n_cgs, cgs, _) -> Hashtbl.hash (ts, (n_cgs, cgs))
        in
        (* Big debug smorgasbord *)
        maybe_debug_hash hash (lazy (
          let open PPrint in
          let open PrintAst in
          string "type arguments" ^^ hardline ^^
          (if ts = [] then string "no types" else separate_map hardline print_typ ts) ^^ hardline ^^
          match extra with
            | Expr (n_cgs, es, _bs) ->
                string "(expr)" ^/^ string (string_of_int n_cgs) ^/^ string "const generics, followed by trait method impl arguments" ^^ hardline ^^
                separate_map hardline (print_expr empty_env) es
            | Cg cgs ->
                string "(type) const generics" ^^ hardline ^^ separate_map hardline print_cg cgs
          ));
        (* Actual Logic *)
        let n = Printf.sprintf "%s_%02x" n (hash land 0xFF) in
        let n = Idents.mk_fresh n (fun n -> Hashtbl.mem seen (m, n)) in
        Hashtbl.add seen (m, n) ();
        (m, n), [ Common.AutoGenerated; gen_comment lid ts extra ]
    else
      let doc =
        separate_map underscore print_typ ts ^^
        (let extra = print_extra extra in if extra <> empty then underscore ^^ extra else empty)
      in
      (fst lid, snd lid ^ KPrint.bsprintf "__%a" PrintCommon.pdoc doc), [ Common.AutoGenerated ]
end

(* Monomorphization of data type definitions **********************************)

(* A whole-program map from type lids to their definitions. *)
let build_def_map files =
  build_map files (fun map -> function
    | DType (lid, flags, _, _, def) ->
        Hashtbl.add map lid (flags, def)
    | _ ->
        ()
  )



(* The type monomorphization phase, below, performs four things at once.
   - First, it monomorphizes data types, by emitting monomorphized definitions
     and replacing references to such polymorphic data types (the  `node`s) with
     references to the corresponding monomorphized declaration (i.e. the `lident`
     found in the `state` for that `node`).
   - Second, it emits forward declarations, to break loops when some types are
     mutually recursive *and* the recursion happens under a pointer.
   - Third, it reorders data type declarations that may have been declared as
     mutually recursive in the source, but for which an order exists that will
     satisfy the C compiler.
   - Fourth, it performs name management by mapping `node`s to `lid`s.

   For the third task, consider that in F* someone may write:

     type t = | T: x:u -> t
     and  u = | U: x:Int32.t -> u

   Thanks to reordering (and leaving aside data type optimizations), this becomes

     typedef struct {
       int x;
     } u;

     typedef struct {
       u x;
     } t;

   This phase additionally establishes some invariants:
   - `node`s do NOT contain any `TApp` -- otherwise, this leads to some
     inconsistent states where we have both `t<u<v>>` and `t<u__v>` in the map
   - everyone must agree on the same name! this was actually the source of bugs
     that were very difficult to track down, especially for type applications of
     the form `t<u<v>>` that appear under a reference, meaning that we must
     allocate a name for `t<u<v>>` (and thus a name for `u<v>`) but *not* visit
     `u<v>`
   
   Operationally, we guarantee some additional behavior, namely, that
   declarations are only reordered *when necessary*. Concretely, we reorder
   declarations as long as our graph traversal does not go through a reference
   (pointer). When it does, we emit a forward declaration (if not done already),
   along with a suitably-chosen name, and remember to emit a monomorphized
   instance of that type later on when we see the polymorphic declaration (via
   the `pending_monomorphizations` table).
*)

include MonomorphizationState

let has_variables ts =
  let r =
    (object
      inherit [_] reduce
      method zero = false
      method plus = (||)
      method! visit_CgVar _ _ =
        true
      method! visit_TCgArray _ _ _ =
        true
      method! visit_TBound _ _ =
        true
    end)#visit_TApp () ([], "") ts
  in
  if r then
    assert !Options.allow_tapps;
  r

let has_cg_array ts =
  let r =
    (object
      inherit [_] reduce
      method zero = false
      method plus = (||)
      method! visit_TCgArray _ _ _ =
        true
    end)#visit_TApp () ([], "") ts
  in
  if r then
    assert !Options.allow_tapps;
  r

let has_cg_variables = List.exists (function CgVar _ -> assert !Options.allow_tapps; true | _ -> false)

let monomorphize_data_types map = object(self)

  inherit [_] map as super

  (* We record pending declarations as we visit top-level declarations. *)
  val mutable pending = []
  (* Current file, for warning purposes. *)
  val mutable current_file = ""
  (* For forward references, a map from lid to its pending monomorphizations
     (type arguments) *)
  val pending_monomorphizations: (lident, (typ list * cg list)) Hashtbl.t = Hashtbl.create 41

  method has_pending_monomorphizations =
    if Options.debug "data-types-traversal" then
      Hashtbl.iter (fun lid (ts, cgs) ->
        KPrint.bprintf "Missing monomorphization: %a\n" ptyp (fold_tapp (lid, ts, cgs))
      ) pending_monomorphizations;
    Hashtbl.length pending_monomorphizations > 0

  (* Record a new declaration. *)
  method private record (d: decl) =
    if Drop.file current_file then
      Warn.(maybe_fatal_error ("", DropDeclaration (lid_of_decl d, current_file)));
    if Options.debug "data-types-traversal" then
      KPrint.bprintf "now pending: %a %a\n" plid (lid_of_decl d) pdecl d;
    pending <- d :: pending

  (* Clear all the pending declarations. *)
  method private clear () =
    let r = List.rev pending in
    pending <- [];
    r

  (* This method produces a type that is *unsuitable* for further passes, since
     it breaks the invariant that type abbreviations are inlined away. It is,
     however, a good candidate for picking a suitable, auto-generated name while
     using existing, previously-picked abbreviations. NB: not doing so will
     generate type errors, see miTLS for a minimal testcase *)
  method pretty (t: typ) =
    (object
      inherit [_] map
      method! visit_TTuple () args =
        match Hashtbl.find state (tuple_lid, args, []) with
        | exception Not_found ->
            let args = List.map (self#visit_typ false) args in
            TTuple args
        | _, chosen_lid ->
            TQualified chosen_lid

      method! visit_TApp () lid args =
        match Hashtbl.find state (lid, args, []) with
        | exception Not_found ->
            let args = List.map (self#visit_typ false) args in
            TApp (lid, args)
        | _, chosen_lid ->
            TQualified chosen_lid
    end)#visit_typ () t

  (* Compute the name of a given node in the graph. *)
  method private lid_of (n: node) =
    let lid, ts, cgs = n in
    if ts = [] && cgs = [] then
      lid, []
    else if List.mem_assoc n !NameGen.distinguished then
      List.assoc n !NameGen.distinguished, []
    else
      NameGen.gen_lid lid ts (Cg cgs)

  method private allocate_names t =
    resolve_deep (fun (lid, args, cgs as node) ->
      if not (Hashtbl.mem state node) then begin
        Hashtbl.add pending_monomorphizations lid (args, cgs);
        Hashtbl.add state node (White, fst (self#lid_of node))
      end;
      true
    ) t

  (* Prettifying the field names for n-uples. *)
  method private field_at i =
    match i with
    | 0 -> "fst"
    | 1 -> "snd"
    | 2 -> "thd"
    | _ -> Printf.sprintf "f%d" i

  method forward_kind lid =
    match Hashtbl.find map lid with
    | exception Not_found ->
        None
    | flags, Union _ ->
        Some (flags, Common.FUnion)
    | flags, _ ->
        Some (flags, FStruct)

  (* Insert a forward struct declaration, with name `chosen_lid` *)
  method private insert_forward chosen_lid forward_kind =
    match forward_kind with
    | None ->
        ()
    | Some (flags, k) ->
        self#record (DType (chosen_lid, flags, 0, 0, Forward k))

  method private mark_if_need_be node chosen_lid =
    match Hashtbl.find_opt state node with
    | Some (BlackForward, _) -> ()
    | _ -> Hashtbl.replace state node (Gray, chosen_lid)

  (* Visit a given node in the graph, modifying [pending] to append in reverse
   * order declarations as they are needed. *)
  method private visit_node (under_ref: bool) (n: node) =
    (* We normalize the type arguments by pre-allocating names. This avoids
       inconsistencies where the map would previously record both t<u<v>> and
       t<u__v> which then required renormalizations and didn't work anyhow.

       Because we have no equirecursive types, this does not loop.

       This has the side-effect of filling the pending_monomorphizations map for
       all names that have been allocated in the process. *)
    let n = fst3 n, List.map self#allocate_names (snd3 n), thd3 n in
    let lid, args, cgs = n in

    match under_ref, Hashtbl.find_opt state n with
    | false, Some (Black, chosen_lid)
    | true, Some ((BlackForward | Black), chosen_lid) ->
        (* A reference to a `node` under a pointer type means that we must
           ensure that the name is in scope. If either a forward declaration or
           a complete declaration were inserted, we have nothing to do. *)
        if Options.debug "data-types-traversal" then
          KPrint.bprintf "skipping %a: Black or (BlackForward under ref)\n" ptyp (fold_tapp n);
        chosen_lid

    | false, Some (Gray, chosen_lid)
    | true, Some ((Gray | White), chosen_lid) ->
        (* Otherwise, we must do something to make sure this name is in scope.
           We do not attempt to reorder the definition. This is the case where
           the type recurses with itself, or the name has been chosen already. *)
        if Options.debug "data-types-traversal" then
          KPrint.bprintf "forward %a: Gray or (White under ref)\n" ptyp (fold_tapp n);
        self#insert_forward chosen_lid (self#forward_kind lid);
        Hashtbl.replace state n (BlackForward, chosen_lid);
        chosen_lid

    | true, None ->
        (* Finally, if we've never visited this node but still need to insert a
           forward declaration, we allocate the name now. *)
        let chosen_lid, flag = self#lid_of n in
        if Options.debug "data-types-traversal" then
          KPrint.bprintf "forward %a: None under ref\n" ptyp (fold_tapp n);
        (* Some logic to try to inherit the flags on the forward declaration
           that the original declaration had (not sure why). *)
        let k =
          match self#forward_kind lid with
          | None -> None
          | Some (flags, k) -> Some (flag @ flags, k)
        in
        self#insert_forward chosen_lid k;
        Hashtbl.replace state n (BlackForward, chosen_lid);
        chosen_lid

    (* Now on to the cases where we are not under a pointer type. Two cases are
       shared with the logic above.
       - false, Black: nothing to do, declaration has been monomorphized already

       - false, Gray: we still insert a forward declaration, for the case below:

         typedef struct s {
           void f(t x);
         } t;

       In all other cases, we have actual work to do: we need to monomorphize
       the declaration, and insert it here to compute a suitable order.
     *)

    | false, (None | Some (White, _) | Some (BlackForward, _) as entry) ->
        (* We have something to do *)
        let chosen_lid, flag = match entry with None -> self#lid_of n | Some (_, lid) -> lid, [] in
        if Options.debug "data-types-traversal" then
          KPrint.bprintf "visiting %a: chosen_lid %a\n" ptyp (fold_tapp n) plid chosen_lid;

        (* Prevent loops and multiple forward declarations *)
        self#mark_if_need_be n chosen_lid;

        let record_and_visit (d: decl) =
          self#record (self#visit_decl false d)
        in

        if lid = tuple_lid then begin
          assert (args <> []);
          let fields = List.mapi (fun i arg -> Some (self#field_at i), (arg, false)) args in
          record_and_visit (DType (chosen_lid, [ Common.Private ], 0, 0, Flat fields));

        end else begin
          let subst fields = List.map (fun (field, (t, m)) ->
            field, (DeBruijn.subst_tn args (DeBruijn.subst_ctn' cgs t), m)
          ) fields in
          assert (not (Hashtbl.mem map lid) || not (has_variables args) && not (has_cg_variables cgs));

          begin match Hashtbl.find map lid with
          | exception Not_found ->
              (* Unknown, external non-polymorphic lid, e.g. Prims.int *)
              ()
          | flags, Variant branches ->
              let branches = List.map (fun (cons, fields) -> cons, subst fields) branches in
              record_and_visit (DType (chosen_lid, flag @ flags, 0, 0, Variant branches))
          | flags, Flat fields ->
              let fields = self#visit_fields_t_opt under_ref (subst fields) in
              record_and_visit (DType (chosen_lid, flag @ flags, 0, 0, Flat fields))
          | flags, Union fields ->
              let fields = List.map (fun (f, t) ->
                let t = DeBruijn.subst_tn args t in
                let t = self#visit_typ under_ref t in
                f, t
              ) fields in
              record_and_visit (DType (chosen_lid, flag @ flags, 0, 0, Union fields))
          | flags, Abbrev t ->
              let t = DeBruijn.subst_tn args t in
              record_and_visit (DType (chosen_lid, flag @ flags, 0, 0, Abbrev t))
          | _ ->
              ()
          end
        end;
        Hashtbl.replace state n (Black, chosen_lid);
        chosen_lid

  method private flush_pending lid =
    List.iter (fun (ts, cgs) ->
      ignore (self#visit_node false (lid, ts, cgs));
      Hashtbl.remove pending_monomorphizations lid
    ) (Hashtbl.find_all pending_monomorphizations lid)

  (* Top-level, non-parameterized declarations are roots of our graph traversal.
   * This also visits, via occurrences in code, applications of parameterized
   * types. *)
  method! visit_file _ file =
    let name, decls = file in
    current_file <- name;
    let decls =
      List.concat_map (fun d ->
        if Options.debug "data-types-traversal" then
          KPrint.bprintf "decl %a\n" plid (lid_of_decl d);
        match d with
        | DType (lid, _, 0, 0, Abbrev (TTuple args)) when not !Options.keep_tuples ->
            let node = tuple_lid, List.map self#allocate_names args, [] in

            if Options.debug "data-types-traversal" then
              KPrint.bprintf "%a abbreviation for %a (%b)\n" plid lid ptyp (TApp (tuple_lid, args)) (Hashtbl.mem state node);

            if Hashtbl.mem state node then
              (* We have already picked a name. Just roll with it. *)
              let d = self#visit_decl false d in
              self#clear () @ [ d ]
            else begin
              Hashtbl.add state node (White, lid);
              assert (self#visit_node false node = lid);
              (* We drop the abbreviation since now the correct type has been
                 emitted with that very name. *)
              self#clear ()
            end

        | DType (lid, _, 0, 0, Abbrev ((TApp _ | TCgApp _) as t)) ->
            (* We have not yet monomorphized this type, and conveniently, we have
               a type abbreviation that provides us with a name hint! We simply
               ditch the type abbreviation and replace it with a monomorphization
               of the same name. *)

            let hd, args, cgs = flatten_tapp t in
            let args = List.map self#allocate_names args in
            let node = hd, args, cgs in

            if Options.debug "data-types-traversal" then
              KPrint.bprintf "%a abbreviation for %a (%b)\n" plid lid ptyp t (Hashtbl.mem state node);

            if Hashtbl.mem state node then
              let d = self#visit_decl false d in
              (* We have already picked a name. Just roll with it. *)
              self#clear () @ [ d ]

            else
              (* miTLS backwards-compat strikes again: if the type is about to be
                 GC'd (i.e. automatically rewritten to be heap-allocated to e.g.
                 support lists "trivially" at the expense of a run-time GC)... then
                 we need to make sure the generated name refers to the GC'd type. So
                 the monomorphized type will be named foobar_gc... *)
              let abbrev_for_gc_type = Hashtbl.mem map hd && List.mem Common.GcType (fst (Hashtbl.find map hd)) in

              let chosen_lid =
                if abbrev_for_gc_type then
                  fst lid, snd lid ^ "_gc"
                else
                  lid
              in
              Hashtbl.add state node (White, chosen_lid);

              assert (self#visit_node false node = chosen_lid);

              (* And a type abbreviation will automatically be rewritten (see
                 GcTypes) into `typedef foobar foobar_gc *`. And mitlsffi.c will be
                 happy. *)
              if abbrev_for_gc_type then
                self#record (DType (lid, [], 0, 0, Abbrev (TQualified chosen_lid)));

              self#clear ()

        | DType (lid, _, n_cgs, n, _) when n > 0 || n_cgs > 0 ->
            (* The type itself cannot be monomorphized, but we may have seen in
               the past monomorphic instances of this type that we ought to
               generate. *)
            self#flush_pending lid;

            (* Leaving this declaration in place to remember where to insert
               pending monomorphizations for this possibly inserted afterwards. *)
            self#clear () @ [ d ]


        | DType (lid, _, n_cgs, n, (Flat _ | Variant _ | Abbrev _ | Union _)) ->
            assert (n = 0 && n_cgs = 0);
            let node = lid, [], [] in
            begin match Hashtbl.find_opt state node with
            | Some (Black, _) ->
                [ d ]
            | _ ->
                self#mark_if_need_be node lid;
                let d = self#visit_decl false d in
                Hashtbl.replace state node (Black, lid);
                self#clear () @ [ d ]
            end

        | _ ->
            (* Not a type, e.g. a global; needs to be retained. *)
            let d = self#visit_decl false d in
            self#clear () @ [ d ]
      ) decls
    in
    (* At this stage, there may still be pending tuples that have occurred
       behind a pointer. We don't have a good heuristic regarding where to place
       such tuples (the definition of tuples is "ambient") so we just flush them
       here at the end of the file. *)
    self#flush_pending tuple_lid;
    name, decls @ self#clear ()

  method! visit_DType env name flags n n_cgs d =
    if n > 0 then
      assert false
    else begin
      super#visit_DType env name flags n n_cgs d
    end

  method! visit_ETuple under_ref es =
    if not !Options.keep_tuples then
      EFlat (List.mapi (fun i e -> Some (self#field_at i), self#visit_expr under_ref e) es)
    else
      super#visit_ETuple under_ref es

  method! visit_PTuple under_ref pats =
    if not !Options.keep_tuples then
      PRecord (List.mapi (fun i p -> self#field_at i, self#visit_pattern under_ref p) pats)
    else
      super#visit_PTuple under_ref pats

  method! visit_TTuple under_ref ts =
    if not !Options.keep_tuples && not (has_variables ts) && not (has_cg_array ts) then
      TQualified (self#visit_node under_ref (tuple_lid, ts, []))
    else
      super#visit_TTuple under_ref ts

  method! visit_TQualified under_ref lid =
    (* FORWARD DECLARATIONS: we force a visit of this node, as it may have a side-effect of
       inserting a forward declaration *)
    TQualified (self#visit_node under_ref (lid, [], []))

  method! visit_TApp under_ref lid ts =
    if Hashtbl.mem map lid && not (has_variables ts) && not (has_cg_array ts) then
      TQualified (self#visit_node under_ref (lid, ts, []))
    else
      super#visit_TApp under_ref lid ts

  method! visit_TCgApp under_ref t cg =
    let lid, ts, cgs = flatten_tapp (TCgApp (t, cg)) in
    if Hashtbl.mem map lid && not (has_variables (List.map (DeBruijn.subst_ctn' cgs) ts)) && not (has_cg_variables cgs) then
      TQualified (self#visit_node under_ref (lid, ts, cgs))
    else
      let ts = List.map (self#visit_typ under_ref) ts in
      fold_tapp (lid, ts, cgs)

  method! visit_TBuf _ t const =
    (* FORWARD DECLARATIONS: we remember that we are underneath a pointer type *)
    TBuf (self#visit_typ true t, const)
end

let datatypes files =
  let map = build_def_map files in
  let o = monomorphize_data_types map in
  let rec do_it files =
    let files = o#visit_files false files in
    (* We may trigger monomorphizations *after* we have seen a declaration. To
       put the pending declarations in the right place, we have to traverse the
       files again anyhow.

       type t a = ...
       let u = t ()
    *)
    if o#has_pending_monomorphizations then
      do_it files
    else
      files
  in
  let files = do_it files in
  let files = List.map (fun (f, decls) ->
    f, List.filter (function
      | DType (_, _, n_cgs, n, _) when n_cgs > 0 || n > 0 ->
          false
      | _ ->
          true
    ) decls
  ) files in
  (* FORWARD DECLARATIONS: because of the convoluted treatment of forward declarations, we have
     nodes in the map with Black and no type or cg arguments. Remove those as it is just very
     confusing for future phases. *)
  Hashtbl.filter_map_inplace (fun k v ->
    match k with
    | _, [], [] -> None
    | _ -> Some v
  ) state;
  files


(* Type monomorphization of functions. ****************************************)

(* This provides a queue of pending monomorphized definitions, that can be cleared when it is
   time for those definitions to be inserted. For type definitions, this functionality is inlined
   within the main visitor. *)
module Gen = struct

  (* Pending definitions *)
  let pending_defs = ref []

  let register_def current_file original_lid cgs ts lid def =
    assert (not (Hashtbl.mem generated_lids (original_lid, cgs, ts)));
    Hashtbl.add generated_lids (original_lid, cgs, ts) lid;
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
    | DFunction (cc, flags, n_cgs, n, t, name, b, body) ->
        if n > 0 || n_cgs > 0 then
          Hashtbl.add map name (`Function (cc, flags, n_cgs, n, t, name, b, body))
    | DGlobal (flags, name, n, t, body) ->
        if n > 0 then
          Hashtbl.add map name (`Global (flags, name, n, t, body))
    | _ ->
        ()
  ) in

  let monomorphize = object(self)

    inherit DeBruijn.map_counting as super

    (* Current file, for warning purposes. *)
    val mutable current_file = ""

    method! visit_file _ file =
      let file_name, decls = file in
      current_file <- file_name;
      file_name, List.concat_map (function
        | DFunction (cc, flags, n_cgs, n, ret, name, binders, body) ->
            if Hashtbl.mem map name then
              []
            else
              let d = DFunction (cc, flags, n_cgs, n, ret, name, binders, self#visit_expr_w 0 body) in
              assert (n = 0 && n_cgs = 0);
              Gen.clear () @ [ d ]
        | DGlobal (flags, name, n, t, body) ->
            if Hashtbl.mem map name then
              []
            else
              let d = DGlobal (flags, name, n, t, self#visit_expr_w 0 body) in
              assert (n = 0);
              Gen.clear () @ [ d ]
        | d ->
            [ d ]
      ) decls

    method! visit_ETApp ((diff, _) as env) e cgs cgs' ts =
      (* Partial cg application generates this *)
      let rec flatten_etapp e =
        match e.node with
        | ETApp (e, cgs, cgs_, ts) ->
            assert (cgs_ = []);
            let e, cgs', ts' = flatten_etapp e in
            e, cgs' @ cgs, ts' @ ts
        | _ ->
            e, [], []
      in
      let e, cgs_, ts_ = flatten_etapp e in
      let cgs, ts = cgs_ @ cgs, ts_ @ ts in

      let fail_if () =
        if cgs @ cgs' <> [] then
          Warn.fatal_error "TODO: e=%a\ncgs=%a\nts=%a\n%a\n"
            pexpr e
            pexprs cgs
            ptyps ts
            pexpr (with_type TUnit (ETApp (e, cgs, cgs', ts)));
      in
      match e.node with
      | EQualified lid ->
          begin try
            (* Already monomorphized? *)
            EQualified (Hashtbl.find generated_lids (lid, cgs @ cgs', ts))
          with Not_found ->
            match Hashtbl.find map lid with
            | exception Not_found ->
                (* External function. Bail. Leave cgs -- treated as normal
                   arguments when going to C. C'est la vie. *)
                if !Options.allow_tapps || AstToCStar.whitelisted_tapp e then
                  super#visit_ETApp env e cgs cgs' ts
                else
                  (self#visit_expr env e).node
            | `Function (cc, flags, n_cgs, n, ret, name, binders, body) ->
                (* Need to generate a new instance. *)
                if n <> List.length ts then begin
                  KPrint.bprintf "%a is not fully type-applied!\n" plid lid;
                  ETApp (self#visit_expr env e, cgs, cgs', ts)
                end else if n_cgs <> List.length cgs then begin
                  KPrint.bprintf "%a is not fully cg-applied!\n" plid lid;
                  ETApp (self#visit_expr env e, cgs, cgs', ts)
                end else
                  (* The thunk allows registering the name before visiting the
                   * body, for polymorphic recursive functions. *)
                  let name, comment = NameGen.gen_lid name ts (Expr (n_cgs, cgs @ cgs', binders)) in
                  let def () =
                    let ret = DeBruijn.(subst_ctn diff cgs (subst_tn ts ret)) in
                    assert (List.length cgs = n_cgs);
                    (* binders are the remaining binders after the cg-binders have been eliminated *)
                    let diff = List.length binders - List.length cgs in
                    let _cg_binders, binders = KList.split (List.length cgs + List.length cgs') binders in
                    let binders = List.map (fun { node; typ; _ } ->
                      { node; typ = DeBruijn.(subst_ctn diff cgs (subst_tn ts typ)); meta = [] }
                    ) binders in
                    (* KPrint.bprintf "about to substitute:\n  e=%a\n  cgs=%a\n cgs'=%a\n  ts=%a\n  head type=%a\n%a\n" *)
                    (*   pexpr e *)
                    (*   pexprs cgs *)
                    (*   pexprs cgs' *)
                    (*   ptyps ts *)
                    (*   ptyp e.typ *)
                    (*   pexpr (with_type TUnit (ETApp (e, cgs, cgs', ts))); *)
                    (* KPrint.bprintf "body: %a\n\n" pexpr body; *)
                    (* KPrint.bprintf "subst_ten ts body: %a\n\n" pexpr DeBruijn.(subst_ten ts body); *)
                    (* KPrint.bprintf "subst_cen diff cgs (subst_ten ts body): %a\n\n" pexpr DeBruijn.(subst_cen diff cgs (subst_ten ts body)); *)
                    let body = DeBruijn.(subst_n' (List.length binders) (subst_cen diff cgs (subst_ten ts body)) cgs') in
                    (* KPrint.bprintf "after substitution: body :%a\n\n" pexpr body; *)
                    let body = self#visit_expr env body in
                    DFunction (cc, flags @ comment, 0, 0, ret, name, binders, body)
                  in
                  EQualified (Gen.register_def current_file lid (cgs @ cgs') ts name def)

            | `Global (flags, name, n, t, body) ->
                fail_if ();
                if n <> List.length ts then begin
                  KPrint.bprintf "%a is not fully type-applied!\n" plid lid;
                  (self#visit_expr env e).node
                end else
                  let name, comment = NameGen.gen_lid name ts (Cg []) in
                  let def () =
                    let t = DeBruijn.subst_tn ts t in
                    let body = DeBruijn.subst_ten ts body in
                    let body = self#visit_expr env body in
                    DGlobal (flags @ comment, name, 0, t, body)
                  in
                  EQualified (Gen.register_def current_file lid [] ts name def)

          end

      | EOp ((K.Eq | K.Neq), _) ->
          assert false

      | EOp (_, _) ->
         (self#visit_expr env e).node

      | _ ->
          KPrint.bprintf "%a is not an lid in the type application\n" pexpr e;
          ETApp (self#visit_expr env e, cgs, cgs', ts)

  end in

  monomorphize#visit_files 0 files


let equalities files =

  let types_map = Helpers.build_map files (fun map d ->
    match d with
    | DType (lid, _, _, _, d) -> Hashtbl.add map lid d
    | _ -> ()
  ) in

  (* I first tried carrying over the map from DataTypes to here, but this map is
     invalidated by the call to GcTypes which results in stale data type definitions
     being left in the map. So, we anticipate a little bit on the result of
     DataTypes.everything here, and just replicate the logic to determine
     whether this is going to end up being an enum or not. *)
  let enum_eventually lid =
    match Hashtbl.find types_map lid with
    | exception Not_found ->
        false
    | Variant branches ->
        List.for_all (fun (_, fields) -> List.length fields = 0) branches
    | _ ->
        false
  in

  let monomorphize = object(self)

    inherit [_] map as _super

    val mutable current_file = ""
    val mutable has_cycle = false

    method! visit_file env file =
      let file_name, decls = file in
      current_file <- file_name;
      file_name, List.concat_map (fun d ->
        let d = self#visit_decl env d in
        let equalities = Gen.clear () in
        let equalities = List.map (function
          | DFunction (cc, flags, n_cgs, n, ret, name, binders, body) ->
              (* This is a highly conservative criterion that is triggered by
               * any recursive type; we could be smarter and only break the
               * cycles by marking ONE declaration public.  *)
              let flags =
                if has_cycle then
                  List.filter ((<>) Common.Private) flags
                else
                  flags
              in
              DFunction (cc, flags, n_cgs, n, ret, name, binders, body)
          | d ->
              d
        ) equalities in
        has_cycle <- false;
        equalities @ [ d ]
      ) decls

    method private maybe_by_addr head x y =
      let t_op, x, y =
        let is_forward = function Some Forward _ -> true | _ -> false in
        match x.typ with
        | TQualified lid when is_forward (Hashtbl.find_opt types_map lid) ->
            let t = TBuf (x.typ, true) in
            TArrow (t, TArrow (t, TBool)), with_type t (EAddrOf x), with_type t (EAddrOf y)
        | _ ->
            let t = x.typ in
            TArrow (t, TArrow (t, TBool)), x, y
      in
      EApp (with_type t_op head, [x;y])

    (* For type [t] and either [op = Eq] or [op = Neq], generate a recursive
     * equality predicate that implements F*'s structural equality. *)
    method private generate_equality t op =
      (* A set of helpers use for generating abstract syntax. *)
      let eq_lid = match op with
        | K.PEq -> [], "__eq"
        | K.PNeq -> [], "__neq"
      in
      let instance_lid, _ = NameGen.gen_lid eq_lid [ t ] (Cg []) in
      let x = fresh_binder "x" t in
      let y = fresh_binder "y" t in

      (* Generate an external to stand in for a user-provided equality operator
         for an external type. *)
      let gen_poly ?(pointer=false) () =
        let t' = if pointer then TBuf (t, true) else t in
        let eq_typ' = TArrow (t', TArrow (t', TBool)) in
        match op with
        | K.PNeq ->
            (* let __neq__t x y = not (__eq__t x y) *)
            let def () =
              let body = mk_not (with_type TBool (
                EApp (with_type eq_typ' (self#generate_equality t K.PEq), [
                  with_type t' (EBound 0); with_type t' (EBound 1) ])))
              in
              DFunction (None, [ Common.Private ], 0, 0, TBool, instance_lid, [ y; x ], body)
            in
            EQualified (Gen.register_def current_file eq_lid [] [ t ] instance_lid def)
        | K.PEq ->
            (* assume val __eq__t: t -> t -> bool *)
            let def () = DExternal (None, [], 0, 0, instance_lid, eq_typ', [ "x"; "y" ]) in
            EQualified (Gen.register_def current_file eq_lid [] [ t ] instance_lid def)
      in


      match t with
      | TQualified ([ "Prims" ], ("int" | "nat" | "pos")) ->
          EOp (K.op_of_poly_comp op, K.CInt)

      | TQualified lid when enum_eventually lid ->
          EPolyComp (op, t)

      | TInt w ->
          EOp (K.op_of_poly_comp op, w)

      | TBool ->
          EOp (K.op_of_poly_comp op, K.Bool)

      | TBuf _ ->
          (* 20210205: I don't think this is allowed anymore, at all. Maybe with
             Steel we'll have raw pointer comparison? Leaving it here just in
             case. *)
          EPolyComp (op, t)

      | TQualified lid when Hashtbl.mem types_map lid ->
          begin try
            (* Already monomorphized? *)
            let existing_lid = Hashtbl.find generated_lids (eq_lid, [], [ t ]) in
            let is_cycle = List.exists (fun d -> lid_of_decl d = existing_lid) !Gen.pending_defs in
            if is_cycle then
              has_cycle <- true;
            EQualified existing_lid
          with Not_found ->
            let mk_conj_or_disj es =
              match op with
              | K.PEq -> List.fold_left mk_and etrue es
              | K.PNeq -> List.fold_left mk_or efalse es
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
                    self#maybe_by_addr (self#generate_equality t op) (with_type t e1) (with_type t e2))
            in
            match Hashtbl.find types_map lid with
            | Abbrev _ | Enum _ | Union _ as e ->
                KPrint.bprintf "Error: did not expect %a\n" ppdef e;
                (* No abbreviations (this runs after inline_type abbrevs).
                 * No Enum / Union / Forward (this runs before data types). *)
                assert false

            | Forward _ ->
                (* Happens when an abstract external type is marked as
                   CAbstractStruct. TODO this is really unpleasant because
                   without the annotation, the type wouldn't be generated at all
                   and would end up "implicitly" external, as in the final case
                   below. *)
                gen_poly ~pointer:true ()

            | Flat fields ->
                (* Either a conjunction of equalities, or a disjunction of inequalities. *)
                let def () =
                  let sub_equalities = List.map (fun (f, (t_field, _)) ->
                    let f = Option.get f in
                    (* __eq__ x.f y.f *)
                    mk_rec_equality t_field
                      (EField (with_type t (EBound 0), f))
                      (EField (with_type t (EBound 1), f))
                  ) fields in
                  DFunction (None, [ Common.Private ], 0, 0, TBool, instance_lid, [ y; x ],
                    mk_conj_or_disj sub_equalities)
                in
                EQualified (Gen.register_def current_file eq_lid [] [ t ] instance_lid def)
            | Variant branches ->
                let def () =
                  let fail_case = match op with
                    | K.PEq -> efalse
                    | K.PNeq -> etrue
                  in
                  (* let __eq__typ y x = *)
                  DFunction (None, [ Common.Private ], 0, 0, TBool, instance_lid, [ y; x ],
                    (* match *)
                    with_type TBool (EMatch (Checked,
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
                        with_type TBool (EMatch (Checked,
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
                EQualified (Gen.register_def current_file eq_lid [] [ t ] instance_lid def)
          end

      | _ ->
          try
            (* Already monomorphized? *)
            EQualified (Hashtbl.find generated_lids (eq_lid, [], [ t ]))
          with Not_found ->
            (* External type without a definition. Comparison of function types? *)
            gen_poly ()

    (* New feature (somewhat unrelated to polymorphic equality
     * monomorphization): generate top-level specialized equalities in case a
     * higher-order occurrence of the equality operator occurs, at a scalar
     * type. *)

    method private eta_expand_op c t =
      let eq_lid = match c with
        | K.PEq -> [], "__eq"
        | K.PNeq -> [], "__neq"
      in
      try
        (* Already monomorphized? *)
        let existing_lid = Hashtbl.find generated_lids (eq_lid, [], [ t ]) in
        EQualified existing_lid
      with Not_found ->
        let eq_typ = TArrow (t, TArrow (t, TBool)) in
        let instance_lid, _ = NameGen.gen_lid eq_lid [ t ] (Cg []) in
        let x = fresh_binder "x" t in
        let y = fresh_binder "y" t in
        EQualified (Gen.register_def current_file eq_lid [] [ t ] instance_lid (fun _ ->
          DFunction (None, [ Common.Private ], 0, 0, TBool, instance_lid, [ y; x ],
            with_type TBool (
              EApp (with_type eq_typ (EPolyComp (c, t)), [
                with_type t (EBound 0); with_type t (EBound 1) ])))))

    method! visit_EApp env e es =
      match e.node, es with
      | EPolyComp (op, t), [ x; y ] ->
          self#maybe_by_addr (self#generate_equality t op) (self#visit_expr env x) (self#visit_expr env y)
      | _ ->
          EApp (self#visit_expr env e, List.map (self#visit_expr env) es)

    method! visit_EPolyComp _ c t =
      (* We are NOT under an application, meaning this is an unapplied equality
         stemming from a higher-order usage of a monomorphic equality operator.
         We perform something similar to `generate_equality` above, namely, we
         register a top-level function that "fills in" for this equality
         function. *)
      self#eta_expand_op c t

  end in

  monomorphize#visit_files () files
