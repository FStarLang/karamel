(** Make sure all structures are passed by reference  **************************)

(* A note on this rewriting. We rewrite:
     f e
   into
     let arg = e in
     f &arg
   Then, in the body of [f], we replace every occurrence of its first formal
   parameter [x] with [*x]. THIS IS LEGAL ONLY BECAUSE STRUCTURES SO FAR ARE
   IMMUTABLE. *)

open Ast
open Common
open PrintAst.Ops

(* This pass assumes that all the desugarings that produce structs have run;
 * that type abbreviations have been removed. *)

(* Construct a [typ -> bool] that tells whether this is a struct type or not. *)
let mk_is_struct files =
  let map = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (function
      | DType (lid, _, Flat _)  ->
          Hashtbl.add map lid true
      | _ ->
          ()
    ) decls
  ) files;
  (* FStar.UInt128.t is a struct only when we have [-fnouint128]. *)
  if not !Options.uint128 then
    Hashtbl.add map ([ "FStar"; "UInt128" ], "t") true;
  function
    | TAnonymous (Flat _) ->
        true
    | TQualified lid ->
        begin try
          Hashtbl.find map lid
        with Not_found ->
          false
        end
    | _ ->
        false

(* Construct a [lid -> bool * bool list]; the first component tells whether
 * the return value of the function should be caller-allocated and passed as the
 * last parameter to the function; the second component tells, for each
 * parameter of the function, whether it has a struct type. *)
let mk_action_table files =
  let is_struct = mk_is_struct files in
  let map = Hashtbl.create 41 in
  List.iter (fun (_, decls) ->
    List.iter (function
      | DFunction (_, _, _, ret, lid, binders, _body) ->
          Hashtbl.add map lid (is_struct ret, List.map (fun b -> is_struct b.typ) binders)
      | DExternal (_, lid, typ) ->
          begin match typ with
          | TArrow _ ->
              let ret, args = Helpers.flatten_arrow typ in
              Hashtbl.add map lid (is_struct ret, List.map is_struct args)
          | _ ->
              ()
          end
      | _ ->
          ()
    ) decls
  ) files;
  map

(* Rewrite a function type to take and possibly return struct pointers. *)
let rewrite_function_type (ret_is_struct, args_are_structs) t =
  let ret, args = Helpers.flatten_arrow t in
  let args = List.map2 (fun arg is_struct ->
    if is_struct then
      TBuf arg
    else
      arg
  ) args args_are_structs in
  let ret, args =
    if ret_is_struct then
      TUnit, args @ [ TBuf ret ]
    else
      ret, args
  in
  Helpers.fold_arrow args ret

let will_be_lvalue e =
  match e.node with
  | EBound _ | EOpen _ | EBufRead _ ->
      true
  | _ ->
      false

exception NotLowStar

(* This function rewrites an application node [e args] into [let x = args in e &args]. It
 * exhibits three behaviors.
 * - If the function is not struct-returning, then no further transformations
 *   occur, the type is preserved, and the expression above is returned.
 * - If the function returns a struct, and [dest] is [None], then the function
 *   returns [let dst in let x = e in f &x &dst; dst], thereby preserving the
 *   type [t] of the expression.
 * - If the function returns a struct, and [dest] is [Some dst], then the
 *   function returns [let x = e in f &x &dst], which has type [unit], and it is
 *   up to the caller to wrap this in a way that preserves the type. *)
let rewrite_app action_table e args dest =
  let lid = Helpers.assert_elid e.node in
  let t, _ = Helpers.flatten_arrow e.typ in

  (* Determine using our computed table which of the arguments and the
   * return type must be passed by reference. We could alternatively use
   * the type of [e], but it sometimes may be incomplete. *)
  let ret_is_struct, args_are_structs = Hashtbl.find action_table lid in

  (* Partial application. Not Low*... bail. This ensures [t] is the return
   * type of the function call. *)
  if List.length args_are_structs <> List.length args then
    raise NotLowStar;

  (* Ensure things remain well-typed. *)
  let e = with_type (rewrite_function_type (ret_is_struct, args_are_structs) e.typ) (EQualified lid) in

  (* At call-site, [f e] can only be transformed into [f &e] is [e] is an
   * [lvalue]. This is, sadly, a little bit of an anticipation over the
   * ast-to-C* translation phase. TODO remove the check, and rely on
   * AstToCStar or a Helpers phase to fix this. *)
  let bs, args = KList.fold_lefti (fun i (bs, es) (e, is_struct) ->
    if is_struct then
      if will_be_lvalue e then
        bs, with_type (TBuf e.typ) (EAddrOf e) :: es
      else
        let x, atom = Helpers.mk_binding (Printf.sprintf "s%d" i) e.typ in
        (x, e) :: bs, with_type (TBuf e.typ) (EAddrOf atom) :: es
    else
      bs, e :: es
  ) ([], []) (List.combine args args_are_structs) in
  let args = List.rev args in

  (* The three behaviors described above. *)
  if ret_is_struct then
    match dest with
    | Some dest ->
        let args = args @ [ with_type (TBuf t) (EAddrOf dest) ] in
        Helpers.nest bs t (with_type TUnit (EApp (e, args)))
    | None ->
        let x, dest = Helpers.mk_binding "ret" t in
        let bs = (x, with_type TAny EAny) :: bs in
        let args = args @ [ with_type (TBuf t) (EAddrOf dest) ] in
        Helpers.nest bs t (with_type t (ESequence [
          with_type TUnit (EApp (e, args));
          dest]))
  else
    Helpers.nest bs t (with_type t (EApp (e, args)))

(* Rewrite functions and expressions to take and possibly return struct
 * pointers. *)
let pass_by_ref action_table = object (self)

  (* We open all the parameters of a function; then, we pass down as the
   * environment the list of atoms that correspond to by-ref parameters. These
   * will have to be "starred". *)
  inherit [Atom.t list] map

  method! dfunction _ cc flags n ret lid binders body =
    (* Step 1: open all the binders *)
    let binders, body = DeBruijn.open_binders binders body in

    let ret_is_struct, args_are_structs = Hashtbl.find action_table lid in

    (* Step 2: rewrite the types of the arguments to take pointers to structs *)
    let binders = List.map2 (fun binder is_struct ->
      if is_struct then
        { binder with typ = TBuf binder.typ }
      else
        binder
    ) binders args_are_structs in

    (* Step 3: add an extra argument in case the return type is a struct, too *)
    let ret, binders, ret_atom =
      if ret_is_struct then
        let ret_binder, ret_atom = Helpers.mk_binding "ret" (TBuf ret) in
        TUnit, binders @ [ ret_binder ], Some ret_atom
      else
        ret, binders, None
    in

    (* ... and remember the corresponding atoms: every occurrence becomes a
     * dereference. *)
    let to_be_starred = KList.filter_map (fun (binder, is_struct) ->
      if is_struct then
        Some binder.node.atom
      else
        None
    ) (List.combine binders (args_are_structs @ (if ret_is_struct then [ false ] else []))) in

    let body = self#visit to_be_starred body in

    (* Step 4: if the function now takes an extra argument for the output struct. *)
    let body =
      if ret_is_struct then
        with_type TUnit (EBufWrite (Option.must ret_atom, Helpers.zerou32, body))
      else
        body
    in
    let body = DeBruijn.close_binders binders body in
    DFunction (cc, flags, n, ret, lid, binders, body)

  method dexternal _ cc lid t =
    match t with
    | TArrow _ ->
        (* Also rewrite external function declarations. *)
        let ret, args = Helpers.flatten_arrow t in
        let ret_is_struct, args_are_structs = Hashtbl.find action_table lid in
        let buf_if arg is_struct = if is_struct then TBuf arg else arg in
        let ret, args =
          if ret_is_struct then
            TUnit, List.map2 buf_if args args_are_structs @ [ TBuf ret ]
          else
            ret, List.map2 buf_if args args_are_structs
        in
        DExternal (cc, lid, Helpers.fold_arrow args ret)
    | _ ->
        DExternal (cc, lid, t)


  method! eopen to_be_starred t name atom =
    (* [x] was a strut parameter that is now passed by reference; replace it
     * with [*x] *)
    if List.exists (Atom.equal atom) to_be_starred then
      EBufRead (with_type (TBuf t) (EOpen (name, atom)), Helpers.zerou32)
    else
      EOpen (name, atom)

  method! eassign to_be_starred _ e1 e2 =
    let e1 = self#visit to_be_starred e1 in
    match e2.node with
    | EApp ({ node = EQualified lid; _ } as e, args) when
      try fst (Hashtbl.find action_table lid) with Not_found -> false ->
        begin try
          let args = List.map (self#visit to_be_starred) args in
          assert (will_be_lvalue e1);
          (rewrite_app action_table e args (Some e1)).node
        with Not_found | NotLowStar ->
          EAssign (e1, self#visit to_be_starred e2)
        end
    | _ ->
        EAssign (e1, self#visit to_be_starred e2)

  method! ebufwrite to_be_starred _ e1 e2 e3 =
    let e1 = self#visit to_be_starred e1 in
    let e2 = self#visit to_be_starred e2 in
    match e3.node with
    | EApp ({ node = EQualified lid; _ } as e, args) when
      try fst (Hashtbl.find action_table lid) with Not_found -> false ->
        begin try
          let args = List.map (self#visit to_be_starred) args in
          let t = Helpers.assert_tbuf e1.typ in
          let dest = with_type t (EBufRead (e1, e2)) in
          (rewrite_app action_table e args (Some dest)).node
        with Not_found | NotLowStar ->
          EBufWrite (e1, e2, self#visit to_be_starred e3)
        end
    | _ ->
        EBufWrite (e1, e2, self#visit to_be_starred e3)

  method! elet to_be_starred t b e1 e2 =
    let e2 = self#visit to_be_starred e2 in
    match e1.node with
    | EApp ({ node = EQualified lid; _ } as e, args) when
      try fst (Hashtbl.find action_table lid) with Not_found -> false ->
        begin try
          let args = List.map (self#visit to_be_starred) args in
          let b, e2 = DeBruijn.open_binder b e2 in
          let e1 = rewrite_app action_table e args (Some (DeBruijn.term_of_binder b)) in
          ELet (b, Helpers.any, DeBruijn.close_binder b (with_type t (
            ESequence [
              e1;
              e2
            ]
          )))
        with Not_found | NotLowStar ->
          ELet (b, self#visit to_be_starred e1, e2)
        end
    | _ ->
        ELet (b, self#visit to_be_starred e1, e2)

  method! eapp to_be_starred _ e args =
    let args = List.map (self#visit to_be_starred) args in
    match e.node with
    | EQualified _ ->
        begin try
          (rewrite_app action_table e args None).node
        with Not_found | NotLowStar ->
          EApp (e, args)
        end
    | _ ->
        EApp (e, args)

end

let pass_by_ref files =
  let action_table = mk_action_table files in
  Helpers.visit_files [] (pass_by_ref action_table) files


(* Explicitly allocate structs in memory, and initialize them in place. This
 * eliminates structure values, and replaces them with pointers; the lifetime of
 * these structs is extended to the enclosing push/pop frame. Copies become
 * explicit.
 * - This allocation scheme is inefficient because offsets are dynamically
 *   computed as we grow the stack. A later phase should collect all
 *   statically-sized buffer allocations and lay them out near the top of the
 *   (in-memory) frame, leaving it up to dynamically-sized buffers to grow the
 *   highwater mark.
 *
 * - The essence of the translation is, for [[e]] a "terminal" node:
 *
 *     [[e: t]] when t is a struct becomes
 *     [[let x: t* = Buffer.create any t 1 in 
 *       alloc_at (e, x); // allocate e at address x
 *       x]]
 *
 *     Terminal nodes that may have struct types are: EAny (!), NOT EApp
 *     (because we just rewrote these above), EFlat, EField.
 *
 *   For non-terminal nodes, such as let:
 *
 *     [[let x: t = e1 in e2]] when t is a struct becomes:
 *     [[let x: t* = e1 in e2]]
 *
 *     Idem for if/then/else and switch.
 *
 *   Finally, some AST nodes may refer to structs now need to deal with pointers:
 *
 *     [[e.f1..fn]] becomes [[e->f1..fn]]
 *     [[addrof e]] becomes [[e]]
 *     [[e1[e2] <- (e3: t)]] becomes a [[blit]]
 *     [[ebuffill]] becomes a for-loop with [[blit]]
 *
 * - The [alloc_at] function (tbd) recursively descends into fields at depth and
 *   knows the current offset where the expression should be written.
 *   The [alloc_at] function may be passed [EAny], in which case it should
 *   generate no instructions.
 *
 * - Some invariants of this transformation.
 *   - Any expression of type [t] where [t] is a struct becomes of type [t*].
 *   - 
 *)

(* Need to roll out this one by hand... because it changes the types. *)
let to_addr is_struct =
  let rec to_addr e =
    let was_struct = is_struct e.typ in
    let not_struct () = assert (not was_struct) in
    let w = with_type e.typ in
    let star_if node =
      if is_struct e.typ then
        { node; typ = TBuf e.typ }
      else
        { node; typ = e.typ }
    in
    match e.node with
    | EBound _
    | EOpen _ ->
        [], star_if e.node
    | EUnit
    | EBool _
    | EString _
    | EQualified _
    | EOp _
    | EConstant _
    | EAny
    | EPushFrame
    | EPopFrame
    | EAbort ->
        not_struct ();
        [], e

    | EWhile (e1, e2) ->
        not_struct ();
        let lb1, e1 = to_addr e1 in
        let lb2, e2 = to_addr e2 in
        lb1 @ lb2, w (EWhile (e1, e2))

    | EFor (b, e1, e2, e3, e4) ->
        not_struct ();
        let lb1, e1 = to_addr e1 in
        let lb2, e2 = to_addr e2 in
        let lb3, e3 = to_addr e3 in
        let lb4, e4 = to_addr e4 in
        lb1 @ lb2 @ lb3 @ lb4, w (EFor (b, e1, e2, e3, e4))

    | EIgnore e ->
        not_struct ();
        let lb, e = to_addr e in
        lb, w (EIgnore e)

    | EApp (e, es) ->
        not_struct ();
        let lb, e = to_addr e in
        let lbs, es = List.split (List.map to_addr es) in
        lb @ List.flatten lbs, w (EApp (e, es))

    | EFlat _ ->
        let b, ref = Helpers.mk_binding "alloc" (TBuf e.typ) in
        [ b, with_type (TBuf e.typ) (EBufCreate (Stack, e, Helpers.oneu32)) ], ref

    | ELet (b, e1, e2) ->
        let b = {
          node = b.node;
          typ = if is_struct b.typ then TBuf b.typ else b.typ
        } in
        let lb1, e1 = to_addr e1 in
        let lb2, e2 = to_addr e2 in
        lb1 @ lb2, star_if (ELet (b, e1, e2))

    | EIfThenElse (e1, e2, e3) ->
        let lb1, e1 = to_addr e1 in
        let lb2, e2 = to_addr e2 in
        let lb3, e3 = to_addr e3 in
        lb1 @ lb2 @ lb3, star_if (EIfThenElse (e1, e2, e3))

    | EAssign (e1, e2) ->
        not_struct ();
        let lb1, e1 = to_addr e1 in
        let lb2, e2 = to_addr e2 in
        lb1 @ lb2, w (EAssign (e1, e2))

    | EBufCreate (l, e1, e2) ->
        (* [e2] will undergo the "allocate at address" treatment later on *)
        let lb1, e1 = to_addr e1 in
        lb1, w (EBufCreate (l, e1, e2))

    | EBufCreateL _ ->
        not_struct ();
        [], e

    | EBufRead (e1, e2) ->
        let lb1, e1 = to_addr e1 in
        let lb2, e2 = to_addr e2 in
        if was_struct then
          lb1 @ lb2, with_type (TBuf e.typ) (EAddrOf (w (EBufRead (e1, e2))))
        else
          lb1 @ lb2, w (EBufRead (e1, e2))

    | EBufWrite (e1, e2, e3) ->
        not_struct ();
        let lb1, e1 = to_addr e1 in
        let lb2, e2 = to_addr e2 in
        lb1 @ lb2, w (EBufWrite (e1, e2, e3))

    | EField (e1, f) ->
        let e1_was_struct = is_struct e1.typ in
        let e1_typ = e1.typ in
        let lb, e1 = to_addr e1 in
        let e1 =
          if e1_was_struct then
            with_type e1_typ (EBufRead (e1, Helpers.zerou32))
          else
            e1
        in
        if was_struct then
          lb, with_type (TBuf e.typ) (EAddrOf (w (EField (e1, f))))
        else
          lb, w (EField (e1, f))

    | EAddrOf e ->
        let was_struct = is_struct e.typ in
        let lb, e = to_addr e in
        if was_struct then
          lb, e
        else
          lb, w (EAddrOf e)

    | EBufSub _
    | EBufBlit _
    | EBufFill _
    | ESwitch _
    | EEnum _
    | EReturn _
    | ECast _
    | EComment _ ->
        Warnings.fatal_error "todo: %a" pexpr e

    | ESequence _
    | ETuple _
    | EMatch _
    | ECons _
    | EFun _ ->
        Warnings.fatal_error "impossible: %a" pexpr e
  in
  object (_self)
    inherit [unit] map

    method! dfunction _ cc flags n ret lid binders body =
      let lbs, body = to_addr body in
      let body = Helpers.nest lbs ret body in
      DFunction (cc, flags, n, ret, lid, binders, body)
  end


let in_memory files =
  (* TODO: do let_to_sequence and sequence_to_let once! *)
  let is_struct = mk_is_struct files in
  let files = Helpers.visit_files () Simplify.sequence_to_let files in
  let files = Helpers.visit_files () (to_addr is_struct) files in
  let files = Helpers.visit_files () Simplify.let_to_sequence files in
  files
