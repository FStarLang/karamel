(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** This module rewrites the original AST to send it into Low*, the subset we
 * know how to translate to C. *)

open Ast
open DeBruijn
open Warn
open PrintAst.Ops
open Helpers

(* A visitor that determines whether it is safe to substitute bound variable 0
 * with its definition, assuming that:
 * - said definition is read-only
 * - there is a single use of it in the continuation.
 * The notion of "safe" can be customized; here, we let EBufRead be a safe node,
 * so by default, safe means read-only. *)
type use = Safe | SafeUse | Unsafe
class ['self] safe_use = object (self: 'self)
  inherit [_] reduce as super

  (* By default, everything is safe. We override several cases below. *)
  method private zero = Safe

  (* The default composition rule; it only applies if the expression itself is
   * safe. (For instance, this is not a valid composition rule for an
   * EBufWrite node.) *)
  method private plus x y =
    match x, y with
    | Safe, SafeUse
    | SafeUse, Safe ->
        SafeUse
    | Safe, Safe ->
        Safe
    | SafeUse, SafeUse ->
        failwith "this contradicts the use-analysis (1)"
    | _ ->
        Unsafe
  method private expr_plus_typ = self#plus

  method! extend j _ =
    j + 1

  (* The composition rule for [es] expressions, whose evaluation order is
   * unspecified, but is known to happen before an unsafe expression. The only
   * safe case is if the use is found among safe nodes. *)
  method private unordered (j, _) es =
    let es = List.map (self#visit_expr_w j) es in
    let the_use, the_rest = List.partition ((=) SafeUse) es in
    match List.length the_use, List.for_all ((=) Safe) the_rest with
    | 1, true -> SafeUse
    | x, _ when x > 1 -> failwith "this contradicts the use-analysis (2)"
    | _ -> Unsafe

  (* The sequential composition rule, where [e1] is known be to be
   * sequentialized before [e2]. Two cases: the use is found in [e1] (and we
   * don't care what happens in [e2]), otherwise, just a regular composition.
   * Note: e2 = Some _ if and only if this is a let-node (hence the + 1). *)
  method private sequential (j, _) e1 e2 =
    match self#visit_expr_w j e1, e2 with
    | SafeUse, _ -> SafeUse
    | x, Some e2 ->
        self#plus x (self#visit_expr_w (j + 1) e2)
    | _, None ->
        (* We don't know what comes after; can't conclude anything. *)
        Unsafe

  method! visit_EBound (j, _) i = if i = j then SafeUse else Safe

  method! visit_EBufWrite env e1 e2 e3 = self#unordered env [ e1; e2; e3 ]
  method! visit_EBufFill env e1 e2 e3 = self#unordered env [ e1; e2; e3 ]
  method! visit_EBufBlit env e1 e2 e3 e4 e5 = self#unordered env [ e1; e2; e3; e4; e5 ]
  method! visit_EBufFree env e = self#sequential env e None
  method! visit_EAssign env e1 e2 = self#unordered env [ e1; e2 ]
  method! visit_EApp env e es =
    match e.node with
    | EOp _ -> super#visit_EApp env e es
    | EQualified _ when Helpers.is_readonly_builtin_lid e -> super#visit_EApp env e es
    | ETApp ({ node = EQualified _; _ } as e, _, _, _) when Helpers.is_readonly_builtin_lid e -> super#visit_EApp env e es
    | _ -> self#unordered env (e :: es)

  method! visit_ELet env _ e1 e2 = self#sequential env e1 (Some e2)
  (* All of the cases below could be refined with a more precise analysis that makes sure that
     *every* path in the control-flow is safe. *)
  method! visit_EIfThenElse env e _ _ = self#sequential env e None
  method! visit_ESwitch env e _ = self#sequential env e None
  method! visit_EWhile env e _ = self#sequential env e None
  method! visit_EFor env _ e _ _ _ = self#sequential env e None
  method! visit_EMatch env _ e _ = self#sequential env e None
  method! visit_ESequence env es = self#sequential env (List.hd es) None
end

let safe_readonly_use e =
  match (new safe_use)#visit_expr_w 0 e with
  | SafeUse -> true
  | Unsafe -> false
  | Safe -> failwith "F* isn't supposed to nest uu__'s this deep, how did we miss it?"

class ['self] safe_pure_use = object (self: 'self)
  inherit [_] reduce as super
  inherit [_] safe_use
  method! visit_EBufRead env e1 e2 = self#unordered env [ e1; e2 ]
  method! visit_EApp env e es =
    match e.node with
    | EOp _ -> super#visit_EApp env e es
    | _ -> self#unordered env (e :: es)
end

let safe_pure_use e =
  match (new safe_pure_use)#visit_expr_w 0 e with
  | SafeUse -> true
  | Unsafe -> false
  | Safe -> failwith "F* isn't supposed to nest uu__'s this deep, how did we miss it?"


(* This phase tries to substitute away variables that are temporary (named
   uu____ in F*, or "scrut" if inserted by the pattern matches compilation
   phase), or that are of a type that cannot be copied (to hopefully skirt
   future failures). This phase assumes the mark field of each binder contains a
   conservative approximation of the number of uses of that binder. *)
let use_mark_to_inline_temporaries = object (self)

  inherit [_] map

  method! visit_ELet _ b e1 e2 =
    let e1 = self#visit_expr_w () e1 in
    let e2 = self#visit_expr_w () e2 in
    let _, v = !(b.node.mark) in
    if (b.node.attempt_inline ||
        Helpers.is_uu b.node.name ||
        b.node.name = "scrut" ||
        Structs.should_rewrite b.typ = NoCopies
       ) &&
        (v = AtMost 1 && (
          is_readonly_c_expression e1 &&
          safe_readonly_use e2 ||
          safe_pure_use e2
        ) ||
        is_readonly_and_variable_free_c_expression e1 && not b.node.mut)
    (* b.node.mut is an approximation of "the address of this variable is taken"
       -- TODO this is somewhat incompatible with the phase that changes size-1
       arrays into variables who address is taken, so we should also check beore
       inlining that the address of this variable is not taken... this is
       starting to be quite an expensive check! *)
    then
      (* Don't drop a potentially useful comment into the ether *)
      let e1 = { e1 with meta = e1.meta @ b.meta } in
      (DeBruijn.subst e1 0 e2).node
    else
      ELet (b, e1, e2)
end

(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

let optimize_lets ?ifdefs files =
  let open UseAnalysis in
  let _ = (build_usage_map_and_mark ifdefs)#visit_files [] files in
  let files = (use_mark_to_remove_or_ignore (not (ifdefs = None)))#visit_files () files in
  let files = use_mark_to_inline_temporaries#visit_files () files in
  files

(* Unused parameter elimination ***********************************************)

(* Done by typing (in general), and based on usage information (strictly for
 * static, first-order functions. Relies on an accurate count from
 * count_and_remove_locals. *)

(* Build a table that maps each lid to a list of booleans, where true indicates
 * that the parameter is unused in the body. *)

let unused_parameter_table = object (_)

  inherit [_] iter

  method! visit_DFunction parameter_table _ flags _ _ _ name binders _ =
    let is_private = List.mem Common.Private flags && not (Helpers.is_static_header name) in
    if is_private then
      let unused_vector = List.map (fun b -> !(b.node.mark)) binders in
      Hashtbl.add parameter_table name unused_vector

end

(* Remove entries in the table if they appear anywhere other than the head of an
 * application. *)

let ignore_non_first_order = object (self)

  inherit [_] iter

  method! visit_EApp env e es =
    List.iter (self#visit_expr env) es;
    let parameter_table, _ = env in
    let _, ts = Helpers.flatten_arrow e.typ in
    match e.node with
    | EQualified lid ->
        (* partial applications are not first-order... may be overly
         * conservative with higher-order code that really means to return a
         * function pointer but that's not the end of the world *)
        if List.length es <> List.length ts then
          Hashtbl.remove parameter_table lid
    | _ -> self#visit_expr env e

  method! visit_EQualified (parameter_table, _) lid =
    if Hashtbl.mem parameter_table lid then
      Hashtbl.remove parameter_table lid

end

(* Now we are ready to effectively remove unused parameters *)

let implies x y =
  not x || y

(* Subtlety: we decline to remove the first parameter if all others are removed,
 * since we don't have zero-argument functions at this stage. *)
let unused private_count_table lid ts (i: int) =
  (* Is the parameter at index i unused? *)
  let unused_i i =
    (* First case: private function (i.e. in the table) that is also unused *)
    Hashtbl.mem private_count_table lid && (
      let l = Hashtbl.find private_count_table lid in
      i < List.length l &&
      snd (List.nth l i) = Mark.AtMost 0
    ) ||
    (* Second case: it's a unit, so here type-based elimination *)
    List.nth ts i = TUnit
  in
  unused_i i &&
  implies (i = 0) (List.exists not (List.init (List.length ts) unused_i))

(* TODO: this is not a fixed point computation, meaning some opportunities for
   unused parameter elimination are missed *)
let remove_unused_parameters = object (self)
  inherit [_] map

  val mutable current_lid = [], ""

  method! extend (table, j) _ =
    table, j + 1

  method! visit_DFunction (parameter_table, _) cc flags n_cgs n ret name binders body =
    current_lid <- name;

    (* Visit first: this may create more unused parameters and modify
     * parameter_table. *)
    let body = self#visit_expr_w (parameter_table, 0) body in

    (* Then eliminate stuff. *)
    let binders = self#visit_binders_w (parameter_table, 0) binders in
    let ret = self#visit_typ (parameter_table, 0) ret in

    let n_binders = List.length binders in
    let ts = List.map (fun b -> b.typ) binders in
    let unused = unused parameter_table name ts in
    let body = List.fold_left (fun body i ->
      if unused i then begin
        DeBruijn.subst eunit (n_binders - 1 - i) body
      end else
        body
    ) body (List.init n_binders (fun i -> i)) in
    let binders = KList.filter_mapi (fun i b -> if unused i then None else Some b) binders in
    DFunction (cc, flags, n_cgs, n, ret, name, binders, body)

  method! visit_DExternal (parameter_table, _ as env) cc flags n_cg n name t hints =
    let ret, args = flatten_arrow t in
    let hints = KList.filter_mapi (fun i arg ->
      if unused parameter_table dummy_lid args i then
        None
      else
        Some arg
    ) hints in
    let args = KList.filter_mapi (fun i arg ->
      if unused parameter_table dummy_lid args i then
        None
      else
        Some (self#visit_typ env arg)
    ) args in
    let ret = self#visit_typ env ret in
    let t = fold_arrow args ret in
    DExternal (cc, flags, n_cg, n, name, t, hints)

  method! visit_TArrow (parameter_table, _ as env) t1 t2 =
    (* Important: the only entries in `parameter_table` are those which are
     * first order, i.e. for which the only occurrence is under an EApp, which
     * does *not* recurse into visit_TArrow! *)
    let t1 = self#visit_typ env t1 in
    let t2 = self#visit_typ env t2 in
    let ret, args = flatten_arrow (TArrow (t1, t2)) in
    let args = KList.filter_mapi (fun i arg ->
      if unused parameter_table dummy_lid args i then
        None
      else
        Some arg
    ) args in
    fold_arrow args ret

  method private update_table_current private_use_table unused i es =
    (* We are currently rewriting the body of [f], which is eligible for
     * use-based unused parameter elimination (because it's private). *)
    if Hashtbl.mem private_use_table current_lid then
      let l = List.length (Hashtbl.find private_use_table current_lid) in
      List.iteri (fun arg_i e ->
        match e.node with
        (* We are currently looking at a function call. The arguments are [es]
         * and each [unused] contains a matching boolean for each one of the [es]. *)
        | EBound j when j >= i && unused arg_i ->
            (* We're about to eliminate [EBound j], which refers to a formal
             * parameter of [f]. This is an opportunity to update the entry for
             * [f]. *)
            Hashtbl.replace private_use_table current_lid
              (List.mapi (fun k (o, Mark.AtMost count) ->
                (* 0 is the last parameter, l - 1 the first *)
                if k == l - 1 - (j - i) then begin
                  assert (count > 0);
                  o, Mark.AtMost (count - 1)
                end else
                  o, Mark.AtMost count
              ) (Hashtbl.find private_use_table current_lid))
        | _ ->
            (* TODO: we could be smarter here *)
            ()
      ) es

  method! visit_EApp ((parameter_table, i), _) e es =
    let t, ts = flatten_arrow e.typ in
    let lid = match e.node with
      | EQualified lid -> lid
      | _ -> [], ""
    in
    let unused = unused parameter_table lid ts in

    let es = List.map (self#visit_expr_w (parameter_table, i)) es in

    self#update_table_current parameter_table unused i es;

    (* Three cases:
     * - more arguments than the type indicates; it's fairly bad, but happens,
     *   e.g. because the function is not in scope (no extract, polymorphic
     *   assume, etc.) -- ignore
     * - as many arguments as the type indicates; perform the transformation
     * - less arguments than the type indicates: perform the transformation on
     *   the arguments we have, transform the type nonetheless *)
    if List.length es <= List.length ts then

      (* Transform the type of the head *)
      let used = List.init (List.length ts) (fun i -> not (unused i)) in
      let ts = KList.filter_mask used ts in
      let ts = List.map (self#visit_typ (parameter_table, 0)) ts in
      let e = { e with typ = fold_arrow ts t } in
      (* Then transform the arguments, on a possible prefix of used when there's
       * a partial application. *)
      let used, _ = KList.split (List.length es) used in
      let es, to_evaluate = List.fold_left2 (fun (es, to_evaluate) used arg ->
        if not used then
          if is_readonly_c_expression arg then
            es, to_evaluate
          else
            let x, _atom = mk_binding "unused" arg.typ in
            es, (x, arg) :: to_evaluate
        else
          arg :: es, to_evaluate
      ) ([], []) used es in
      let es = List.rev es in
      let to_evaluate = List.rev to_evaluate in
      (* Special case: we allow a partial application over an eliminated
       * argument to become a reference to a function pointer. Useful for
       * functions that take regions but that we still want to use as function
       * pointers. *)
      let e = self#visit_expr_w (parameter_table, i) e in
      let app = if List.length es > 0 then with_type t (EApp (e, es)) else e in
      (nest to_evaluate t app).node
    else
      EApp (self#visit_expr_w (parameter_table, i) e, es)
end


(* Get wraparound semantics for arithmetic operations using casts to uint_* ***)

let wrapping_arithmetic = object (self)

  inherit [_] map

  (* TODO: this is no longer exposed by F*; check and remove this pass? *)
  method! visit_EApp env e es =
    match e.node, es with
    | EOp (((K.AddW | K.SubW | K.MultW | K.DivW) as op), w), [ e1; e2 ] when K.is_signed w ->
        let unsigned_w = K.unsigned_of_signed w in
        let e = mk_op (K.without_wrap op) unsigned_w in
        let e1 = self#visit_expr env e1 in
        let e2 = self#visit_expr env e2 in
        let c e = { node = ECast (e, TInt unsigned_w); typ = TInt unsigned_w; meta = [] } in
        (** TODO: the second call to [c] is optional per the C semantics, but in
         * order to preserve typing, we have to insert it... maybe recognize
         * that pattern later on at the C emission level? *)
        let unsigned_app = { node = EApp (e, [ c e1; c e2 ]); typ = TInt unsigned_w; meta = [] } in
        ECast (unsigned_app, TInt w)

    | EOp (((K.AddW | K.SubW | K.MultW | K.DivW) as op), w), [ e1; e2 ] when K.is_unsigned w ->
        let e = mk_op (K.without_wrap op) w in
        let e1 = self#visit_expr env e1 in
        let e2 = self#visit_expr env e2 in
        EApp (e, [ e1; e2 ])

    | _, es ->
        EApp (self#visit_expr env e, List.map (self#visit_expr env) es)
end


let remove_ignore_unit = object

  inherit [_] map as super

  method! visit_EApp env hd args =
    match hd.node, args with
    | ETApp ({ node = EQualified (["LowStar"; "Ignore"], "ignore"); _}, _, _, [ TUnit ]), [ { node = EUnit; _ } ] ->
        EUnit
    | _ ->
        super#visit_EApp env hd args
end

let remove_proj_is = object

  inherit [_] map

  method! visit_DFunction _ cc flags n_cgs n t name binders body =
    if KString.starts_with (snd name) "__proj__" || KString.starts_with (snd name) "__is__" then
      DFunction (cc, Private :: flags, n_cgs, n, t, name, binders, body)
    else
      DFunction (cc, flags, n_cgs, n, t, name, binders, body)
end


(* Convert back and forth between [e1; e2] and [let _ = e1 in e2]. ************)

let sequence_to_let = object (self)

  inherit [_] map

  method! visit_ESequence env es =
    let es = List.map (self#visit_expr env) es in
    match List.rev es with
    | last :: first_fews ->
        (List.fold_left (fun cont e ->
          { node = ELet (sequence_binding (), e, lift 1 cont); typ = last.typ; meta = [] }
        ) last first_fews).node
    | [] ->
        failwith "[sequence_to_let]: impossible (empty sequence)"

  method! visit_EIgnore (env, t) e =
    (nest_in_return_pos t (fun _ e -> with_type t (EIgnore (self#visit_expr_w env e))) e).node

end

let let_to_sequence = object (self)

  inherit [_] map

  method! visit_ELet env b e1 e2 =
    match b.node.meta with
    | Some MetaSequence ->
        let e1 = self#visit_expr env e1 in
        let _, e2 = open_binder b e2 in
        let e2 = self#visit_expr env e2 in
        begin match e1.node, e2.node with
        | _, EUnit ->
            (* let _ = e1 in () *)
            e1.node
        | ECast ({ node = EUnit; _ }, _), _
        | EUnit, _ ->
            (* let _ = () in e2 *)
            e2.node
        | _, ESequence es ->
            ESequence (e1 :: es)
        | _ ->
            ESequence [e1; e2]
        end
    | None ->
        let e2 = self#visit_expr env e2 in
        ELet (b, e1, e2)

end

(* This pass rewrites:
 *   let x = if ... then e else e'
 * into:
 *   let x = any;
 *   if ... then
 *     x <- e
 *   else
 *     x <- e'
 *
 * The code is prettier if we push the assignment under lets, ifs and switches.
 * We also rewrite:
 *   x <- if ... then ...
 * the same way. *)
let let_if_to_assign = object (self)

  inherit [_] map

  method private make_assignment lhs e1 =
    let nest_assign = nest_in_return_pos TUnit (fun i innermost -> {
      node = EAssign (DeBruijn.lift i lhs, innermost);
      typ = TUnit; meta = []
    }) in
    match e1.node with
    | EIfThenElse (cond, e_then, e_else) ->
        let e_then = nest_assign (self#visit_expr_w () e_then) in
        let e_else = nest_assign (self#visit_expr_w () e_else) in
        with_unit (EIfThenElse (cond, e_then, e_else))

    | ESwitch (e, branches) ->
        let branches = List.map (fun (tag, e) ->
          tag, nest_assign (self#visit_expr_w () e)
        ) branches in
        with_unit (ESwitch (e, branches))

    | _ ->
        invalid_arg "make_assignment"

  method! visit_ELet (_, t) b e1 e2 =
    match e1.node, b.node.meta with
    | (EIfThenElse _ | ESwitch _), None ->
        (* [b] holds the return value of the conditional *)
        let b = mark_mut b in
        let e = self#make_assignment (with_type b.typ (EBound 0)) (DeBruijn.lift 1 e1) in
        ELet (b, any, with_type t (
          ELet (sequence_binding (), e, DeBruijn.lift 1 (self#visit_expr_w () e2))))

    | _ ->
        (* This may be a statement-let; visit both. *)
        ELet (b, self#visit_expr_w () e1, self#visit_expr_w () e2)

  method! visit_EAssign _ e1 e2 =
    match e2.node with
    | (EIfThenElse _ | ESwitch _) ->
        (self#make_assignment e1 e2).node

    | _ ->
        EAssign (e1, e2)
end

(* Transform functional updates of the form x.(i) <- { x.(i) with f = e } into
 * in-place field updates. *)
let functional_updates = object (self)

  inherit [_] map as super

  val mutable make_mut = []

  (* TODO: there are many combinations of operators or not (both for reading and writing), a single
     assignment or not... we don't cover everything *)

  method private gen_assignments env e_read exprfields =
    ESequence (List.map (fun (the_field, the_expr) ->
      let the_field = Option.get the_field in
      let the_expr = self#visit_expr env the_expr in
      make_mut <- (assert_tlid e_read.typ, the_field) :: make_mut;
      with_unit (EAssign (with_type the_expr.typ (EField (e_read, the_field)), the_expr))
    ) exprfields)

  method! visit_EApp env e es =
    (* Without temporary, any position, support for multiple fields updated

       e1 *= { fi = ei } with ei = e if i = k, e1[0].fi otherwise
       -->
       e1 *= e

       e1 *= { fi = ei } with ei = e if i = k, !*e1.fi otherwise
       -->
       e1 *= e

     *)
    match e.node, es with
    | EQualified (["LowStar"; "BufferOps"], op), [ e1; { node = EFlat fields; _ }] when KString.starts_with op "op_Star_Equal" ->
        let updated_fields, untouched_fields = List.partition (function
            | Some f, { node = EField ({ node = EBufRead (e1', e2); _ }, f'); _ } when
              f = f' && e1 = e1' && Helpers.is_zero e2 ->
                false
            | Some f, { node = EField ({
                node = EApp ({
                  node = EQualified (["LowStar"; "BufferOps"], op); _
                },
                [ e1' ]); _
              }, f'); _ } when
              (* we match: !*e_deref.f' and request e_read = BufRead (e_deref, 0) *)
              f = f' && e1 = e1' && KString.starts_with op "op_Bang_Star" ->
                false
            | _ ->
                true
          ) fields
        in
        if List.length untouched_fields > 0 then
          (* TODO: catch the monomorphized name of the *= operator above and use that for prettier
             code-gen *)
          let e_read = with_type (assert_tbuf e1.typ) (EBufRead (e1, Helpers.zerou32)) in
          self#gen_assignments env e_read updated_fields
        else
          super#visit_EApp env e es
    | _ ->
        super#visit_EApp env e es

  method! visit_EBufWrite env e1 e2 e3 =
    (* Without temporary, any position, support for multiple fields updated

       e1[e2] <- { fi = ei } with ei = e if i = k, e1[e2].fi otherwise
       -->
       e1[e2].fk <- e

       e1[0] <- { fi = ei } with ei = e if i = k, !*e1.fi otherwise
       -->
       e1[0].fk <- e

     *)
    let e_read = EBufRead (e1, e2) in
    match e3.node with
    | EFlat fields ->
        let updated_fields, untouched_fields = List.partition (function
            | Some f, { node = EField (e_read', f'); _ } when f = f' && e_read = e_read'.node ->
                false
            | Some f, { node = EField ({
                node = EApp ({
                  node = EQualified (["LowStar"; "BufferOps"], op); _
                },
                [ e_deref ]); _
              }, f'); _ } when
              (* we match: !*e_deref.f' and request e_read = BufRead (e_deref, 0) *)
              f = f' && e1 = e_deref && Helpers.is_zero e2 && KString.starts_with op "op_Bang_Star" ->
                false
            | _ ->
                true
          ) fields
        in
        if List.length untouched_fields > 0 then
          self#gen_assignments env (with_type (assert_tbuf e1.typ) e_read) updated_fields
        else
          super#visit_EBufWrite env e1 e2 e3
    | _ ->
        super#visit_EBufWrite env e1 e2 e3


  method! visit_ELet env b e1 e2 =
    let b = self#visit_binder env b in
    let e1 = self#visit_expr env e1 in

    let make_assignment fields k =
      let updated_fields, untouched_fields = List.partition (function
          | Some f, { node = EField ({ node = EBound 0; _ }, f'); _ } when f = f' ->
              false
          | _ ->
              true
        ) fields
      in
      if List.length untouched_fields > 0 then
        let updated_fields = List.map (fun (f, e) -> f, snd (open_binder b e)) updated_fields in
        k (self#gen_assignments env e1 updated_fields)
      else
        ELet (b, e1, self#visit_expr env e2)
    in

    (* TODO: operators *)
    match e1.node, e2.node with
    | EBufRead ({ node = EBound i; _ }, j),
      EBufWrite ({ node = EBound iplusone; _ }, j', { node = EFlat fields; _ })
      when j = j' && iplusone = i + 1 ->
        (* With temporary, in terminal position:

           let uu = (Bound i)[j] in
           (Bound (i + 1))[j] <- { fi = ei } with ei = e if i = k, (Bound 0).fi otherwise
           -->
           (Bound i)[j].fk <- (unlift 1 e)
         *)
        make_assignment fields (fun x -> x)

    | EBufRead ({ node = EBound i; _ }, j),
      ELet (b,
        { node = EBufWrite ({ node = EBound iplusone; _ }, j', { node = EFlat fields; _ }); _ },
        e3)
      when j = j' && iplusone = i + 1 ->
        (* With temporary, NOT in terminal position:

           let uu = (Bound i)[j];
           let _ = (Bound (i + 1))[j] <- { fi = ei } with ei = e if i = k, * (Bound 0).fi otherwise in
           e3
           -->
           let _ = (Bound i)[j].fk <- (unlift 1 e) in
           e3
         *)
        make_assignment fields (fun x ->
          let e3 = self#visit_expr env (snd (open_binder b e3)) in
          ELet (b, with_unit x, e3))

    | _ ->
        ELet (b, e1, self#visit_expr env e2)

  (* The same object is called a second time with the mark_mut flag set to true
   * to mark those fields that now ought to be mutable *)
  method! visit_DType mark_mut name flags n_cgs n def =
    match def with
    | Flat fields when mark_mut ->
        let fields = List.map (fun (f, (t, m)) ->
          if List.exists (fun (name', f') -> Some f' = f && name' = name) make_mut then
            f, (t, true)
          else
            f, (t, m)
        ) fields in
        DType (name, flags, n_cgs, n, Flat fields)
    | _ ->
        DType (name, flags, n_cgs, n, def)
end

let mutated_types = Hashtbl.create 41

let misc_cosmetic = object (self)

  inherit [_] map as super

  val mutable count = 0

  method! visit_ELet env b e1 e2 =
    let b = self#visit_binder env b in
    let e1 = self#visit_expr env e1 in
    (* We cannot optimize aligned types, because CStarToC11 is only inserting alignment directives
       on arrays, not local variables. *)
    let is_aligned = match e1.typ with
      | TQualified lid when Helpers.is_aligned_type lid ->
          true
      | _ ->
          false
    in
    match e1.node with
    | EBufCreate (Common.Stack, e1, { node = EConstant (_, "1"); _ }) when not (Options.wasm () || Options.rust ()) && not is_aligned ->
        (* int x[1]; x[0] = e; x
         * -->
         * int x; x = e; &x *)
        let t = assert_tbuf_or_tarray b.typ in
        let b = with_type t { b.node with mut = true } in
        let ref = with_type (TBuf (t, false)) (EAddrOf (with_type t (EBound 0))) in
        ELet (b, e1, self#visit_expr env (DeBruijn.subst_no_open ref 0 e2))

    | _ ->

        (* let x = $any in
              ^^   ^^^
              b     e1
           let _  = f  (&x) in // sequence
              ^^    ^^
              b'    e3
           p[k] <- { ... f: x ... }
           ^^     ^^^^^^^^^^^^^
           e4         fs
           -->
           f (&p[k].f);
           p[k].f' <- e'
        *)
        match e1.node, e2.node with
        | EAny, ELet (b', { node = EApp (e3, [ { node = EAddrOf ({ node = EBound 0; _ }); _ } ]); _ },
            { node = EBufWrite (e4, e4_index, { node = EFlat fields; _ }); _ })
          when b'.node.meta = Some MetaSequence &&
          List.exists (fun (f, x) -> f <> None && x.node = EBound 1) fields &&
          Mark.is_atmost 2 (snd !(b.node.mark)) ->

            (* if true then Warn.fatal_error "MATCHED: %a" pexpr (with_unit (ELet (b, e1, e2))); *)

            let f, { typ = x_typ; _ } = List.find (fun (_, x) -> x.node = EBound 1) fields in
            let f = Option.get f in

            let e3 = snd (DeBruijn.open_binder b e3) in
            let e4 = snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e4))) in
            let e4_index = snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e4_index))) in
            let fields = List.map (fun (f, e) -> f, snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e)))) fields in

            let e4_typ = assert_tbuf e4.typ in
            Hashtbl.add mutated_types (assert_tlid e4_typ) ();
            let e4 = with_type e4_typ (EBufRead (e4, e4_index)) in

            ESequence (
              with_unit (EApp (e3, [
                with_type (TBuf (x_typ, false)) (EAddrOf (
                  with_type x_typ (EField (e4, f))))])) ::
              List.filter_map (fun (f', e) ->
                let f' = Option.get f' in
                if f = f' then
                  None
                else
                  Some (with_unit (EAssign (
                    with_type e.typ (EField (e4, f')),
                    e)))
              ) fields)

        (* let x;
           f(&x);
           p[k] <- { ... f: x ... };
           ...
           -->
           f (&p[k].f);
           p.f' <- e';
           ...

           (Same as above, but in non-terminal position)
        *)
        | EAny, ELet (b', { node = EApp (e3, [ { node = EAddrOf ({ node = EBound 0; _ }); _ } ]); _ },
            { node = ELet (b'', { node = EBufWrite (e4, e4_index, { node = EFlat fields; _ }); _ }, e5); _ })
          when b'.node.meta = Some MetaSequence &&
          b''.node.meta = Some MetaSequence &&
          List.exists (fun (f, x) -> f <> None && x.node = EBound 1) fields &&
          Mark.is_atmost 2 (snd !(b.node.mark)) ->

            (* if true then Warn.fatal_error "MATCHED: %a" pexpr (with_unit (ELet (b, e1, e2))); *)

            let f, { typ = x_typ; _ } = List.find (fun (_, x) -> x.node = EBound 1) fields in
            let f = Option.get f in

            let e3 = snd (DeBruijn.open_binder b e3) in
            let e4 = snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e4))) in
            let e4_index = snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e4_index))) in
            let fields = List.map (fun (f, e) -> f, snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e)))) fields in

            let e4_typ = assert_tbuf e4.typ in
            Hashtbl.add mutated_types (assert_tlid e4_typ) ();
            let e4 = with_type e4_typ (EBufRead (e4, e4_index)) in

            let e5 = self#visit_expr env e5 in

            ESequence (
              with_unit (EApp (e3, [
                with_type (TBuf (x_typ, false)) (EAddrOf (
                  with_type x_typ (EField (e4, f))))])) ::
              List.filter_map (fun (f', e) ->
                let f' = Option.get f' in
                if f = f' then
                  None
                else
                  Some (with_unit (EAssign (
                    with_type e.typ (EField (e4, f')),
                    e)))
              ) fields @
              [ e5 ])

        (* let x = $any in
              ^^   ^^^
              b     e1
           let _  = f  (&x) in // sequence
              ^^    ^^
              b'    e3
           p := x
           ^^
           e4
           -->
           f (&p);
           ...
        *)
        | EAny, ELet (b', { node = EApp (e3, [ { node = EAddrOf ({ node = EBound 0; _ }); _ } ]); _ },
            { node = EAssign (e4, { node = EBound 1; _ }); _ })
          when b'.node.meta = Some MetaSequence &&
          Mark.is_atmost 2 (snd !(b.node.mark)) ->

            (* KPrint.bprintf "MATCHED: %a" pexpr (with_unit (ELet (b, e1, e2))); *)

            let e3 = snd (DeBruijn.open_binder b e3) in
            let e4 = snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e4))) in

            EApp (e3, [ with_type (TBuf (e4.typ, false)) (EAddrOf e4)])

        (* let x = $any in
           let _ = f(&x) in
           let _ = p := x in
           ...

           (same as above but not in non-terminal position) *)
        | EAny, ELet (b',
            { node = EApp (e3, [ { node = EAddrOf ({ node = EBound 0; _ }); _ } ]); _ },
            { node = ELet (b'', { node = EAssign (e4, { node = EBound 1; _ }); _ }, e5); _ })
          when b'.node.meta = Some MetaSequence &&
          Mark.is_atmost 2 (snd !(b.node.mark)) ->

            (* KPrint.bprintf "MATCHED: %a" pexpr (with_unit (ELet (b, e1, e2))); *)

            let e3 = snd (DeBruijn.open_binder b e3) in
            let e4 = snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e4))) in
            let e5 = snd (DeBruijn.open_binder b (snd (DeBruijn.open_binder b' e5))) in

            ELet (b'', with_unit (EApp (e3, [ with_type (TBuf (e4.typ, false)) (EAddrOf e4)])), self#visit_expr env e5)

        | _, _ ->
            ELet (b, e1, self#visit_expr env e2)

  (* Turn empty then branches into empty else branches to get prettier syntax
   * later on. *)
  method! visit_EIfThenElse env e1 e2 e3 =
    let e1 = self#visit_expr env e1 in
    let e2 = self#visit_expr env e2 in
    let e3 = self#visit_expr env e3 in
    match e2.node with
    | EUnit when e3.node <> EUnit ->
        (* TODO: if e1 is an equality, make it a != *)
        EIfThenElse (Helpers.mk_not e1, e3, e2)
    | _ ->
        EIfThenElse (e1, e2, e3)

  (* &x[0] --> x *)
  method! visit_EAddrOf env e =
    let e = self#visit_expr env e in
    match e.node with
    | EBufRead (e, { node = EConstant (_, "0"); _ }) ->
        e.node
    | _ ->
        EAddrOf e

  method! visit_EBufRead env e1 e2 =
    let e1 = self#visit_expr env e1 in
    let e2 = self#visit_expr env e2 in
    match e1.node, e2.node with
    | EAddrOf e, EConstant (_, "0") ->
        e.node
    | _ ->
        EBufRead (e1, e2)

  method! visit_EBufWrite env e1 e2 e3 =
    let e1 = self#visit_expr env e1 in
    let e2 = self#visit_expr env e2 in
    let e3 = self#visit_expr env e3 in
    match e1.node, e2.node with
    | EAddrOf e, EConstant (_, "0") ->
        EAssign (e, e3)
    | _ ->
        EBufWrite (e1, e2, e3)

  method! visit_EBufSub env e1 e2 =
    (* AstToCStar emits BufSub (e, 0) as just e, so we need the value
     * check to be in agreement on both sides. *)
    match e2.node with
    | EConstant (_, "0") when not (Options.rust ()) ->
        (self#visit_expr env e1).node
    | _ ->
        EBufSub (self#visit_expr env e1, self#visit_expr env e2)

  (* renumber uu's to have a stable numbering scheme that minimizes the diff
   * from one code generation to another *)
  method! visit_decl env decl =
    count <- 0;
    super#visit_decl env decl

  method! visit_binder _ binder =
    if Helpers.is_uu binder.node.name then
      let c = count in
      count <- count + 1;
      { binder with node = { binder.node with name = "uu____" ^ string_of_int c }}
    else
      binder

end

let misc_cosmetic2 = object
  inherit [_] map
  method! visit_DType () name flags n_cgs n def =
    match def with
    | Flat fields when Hashtbl.mem mutated_types name ->
        DType (name, flags, n_cgs, n, Flat (List.map (fun (f, (t, _)) -> f, (t, true)) fields))
    | _ ->
        DType (name, flags, n_cgs, n, def)
end

(* No left-nested let-bindings ************************************************)

(* This function returns an expression that can successfully be translated as a
 * C* statement, after going through let-if-to-assign conversion.
 * - This function shall be called wherever statements are expected (function
 *   bodies; then/else branches; branches of switches).
 * - It returns a series of let-bindings nested over an expression in terminal
 *   position.
 * - It guarantees that if-then-else nodes appear either in statement position,
 *   or immediately under a let-binding, meaning they will undergo
 *   let-if-to-assign conversion. *)
type pos =
  | UnderStmtLet
  | UnderConditional
  | Unspecified

(* Enforce short-circuiting semantics for boolean operators; in C, this means
 * erroring out, and in Wasm, this means nesting let-bindings for the rhs
 * underneath. *)
let rec flag_short_circuit loc t e0 es =
  let lhs0, e0 = hoist_expr loc Unspecified e0 in
  let lhss, es = List.split (List.map (hoist_expr loc Unspecified) es) in
  match e0.node, es, lhss with
  | EOp ((K.And | K.Or) as op, K.Bool), [ e1; e2 ], [ lhs1; lhs2 ] ->
      (* In Wasm, we automatically inline functions based on their size, so we
       * can't ask the user to rewrite, but it's ok, because it's an expression
       * language, so we can have let-bindings anywhere. *)
      if List.length lhs2 > 0 && not (Options.wasm ()) then begin
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc loc,
          GeneratesLetBindings (
            KPrint.bsprintf "%a, a short-circuiting boolean operator" pexpr e0,
            with_type t (EApp (e0, es)),
            lhs2)));
        match op with
        | K.And ->
            lhs1, with_type t (EIfThenElse (e1, nest lhs2 e2.typ e2, efalse))
        | K.Or ->
            lhs1, with_type t (EIfThenElse (e1, etrue, nest lhs2 e2.typ e2))
        | _ ->
            assert false
      end else
        lhs1, with_type t (EApp (e0, [ e1; nest lhs2 e2.typ e2 ]))
  | _ ->
      let lhs = lhs0 @ List.flatten lhss in
      lhs, with_type t (EApp (e0, es))

(* When allocating an array, whether the initial elements of the array need to
   be hoisted depend on the type; if it's an array of pointers, yes, we host. If
   it's an array of arrays, we leave initializer lists in order to fill storage.
   *)
and maybe_hoist_initializer loc t e =
  match e.node with
  | EBufCreate _ when Helpers.is_array t ->
      failwith "expected EBufCreateL here"
  | EBufCreateL (l, es) when Helpers.is_array t ->
      let lhs, es = List.split (List.map (maybe_hoist_initializer loc (Helpers.assert_tarray t)) es) in
      let lhs = List.flatten lhs in
      lhs, with_type t (EBufCreateL (l, es))
  | _ ->
      hoist_expr loc Unspecified e

and hoist_stmt loc e =
  let mk = with_type e.typ in
  match e.node with
  | EApp (e0, es) ->
      (* A call is allowed in terminal position regardless of whether it has
       * type unit (generates a statement) or not (generates a [EReturn expr]). *)
      let lhs, e = flag_short_circuit loc e.typ e0 es in
      nest lhs e.typ e

  | ELet (binder, e1, e2) ->
      (* When building a statement, let-bindings may nest right but not left. *)
      let lhs, e1 = hoist_expr loc UnderStmtLet e1 in
      let binder, e2 = open_binder binder e2 in
      let e2 = hoist_stmt loc e2 in
      nest lhs e.typ (mk (ELet (binder, e1, close_binder binder e2)))

  | EIfThenElse (e1, e2, e3) ->
      let lhs, e1 = hoist_expr loc Unspecified e1 in
      let e2 = hoist_stmt loc e2 in
      let e3 = hoist_stmt loc e3 in
      nest lhs e.typ (mk (EIfThenElse (e1, e2, e3)))

  | EMatch (f, e1, branches) ->
      let lhs, e1 = hoist_expr loc Unspecified e1 in
      let branches = List.map (fun (binders, p, e2) ->
        let binders, e2 = open_binders binders e2 in
        binders, p, close_binders binders (hoist_stmt loc e2)
      ) branches in
      nest lhs e.typ (mk (EMatch (f, e1, branches)))

  | ESwitch (e1, branches) ->
      let lhs, e1 = hoist_expr loc Unspecified e1 in
      let branches = List.map (fun (tag, e2) -> tag, hoist_stmt loc e2) branches in
      nest lhs e.typ (mk (ESwitch (e1, branches)))

  | EFor (binder, e1, e2, e3, e4) ->
      assert (e.typ = TUnit);
      (* The semantics is that [e1] is evaluated once, so it's fine to hoist any
       * let-bindings it generates. *)
      let lhs1, e1 = hoist_expr loc (if binder.node.meta = Some MetaSequence then UnderStmtLet else Unspecified) e1 in
      let binder, s = opening_binder binder in
      let e2 = s e2 and e3 = s e3 and e4 = s e4 in
      (* [e2] and [e3], however, are evaluated at each loop iteration! *)
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      let lhs3, e3 = hoist_expr loc UnderStmtLet e3 in
      (* Note: this should always be a fatal error when going to C, but only for
         the for-loop (since there is no workaround like for the if-then-else
         case. *)
      if lhs2 <> [] || lhs3 <> [] then
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc loc,
          GeneratesLetBindings ("this for-loop's condition or iteration", e, (lhs2 @ lhs3))));
      let e4 = hoist_stmt loc e4 in
      let s = closing_binder binder in
      (* If we get here let-bindings are ok for the chosen backend, likely wasm
         or rust *)
      nest lhs1 e.typ (mk (EFor (binder, e1, s (nest lhs2 e2.typ e2), s (nest lhs3 e3.typ e3), s e4)))

  | EWhile (e1, e2) ->
      (* All of the following cases are valid statements (their return type is
       * [TUnit]. *)
      let lhs, e1 = hoist_expr loc Unspecified e1 in
      if lhs <> [] then
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc loc,
          GeneratesLetBindings ("this while-loop's test expression", e, lhs)));
      let e2 = hoist_stmt loc e2 in
      mk (EWhile (e1, e2))

  | EAssign (e1, e2) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      nest (lhs1 @ lhs2) e.typ (mk (EAssign (e1, e2)))

  | EBufWrite (e1, e2, e3) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      let lhs3, e3 = hoist_expr loc Unspecified e3 in
      nest (lhs1 @ lhs2 @ lhs3) e.typ (mk (EBufWrite (e1, e2, e3)))

  | EBufBlit (e1, e2, e3, e4, e5) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      let lhs3, e3 = hoist_expr loc Unspecified e3 in
      let lhs4, e4 = hoist_expr loc Unspecified e4 in
      let lhs5, e5 = hoist_expr loc Unspecified e5 in
      nest (lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5) e.typ (mk (EBufBlit (e1, e2, e3, e4, e5)))

  | EReturn e ->
      let lhs, e = hoist_expr loc Unspecified e in
      nest lhs e.typ (mk (EReturn e))

  | EBreak ->
      mk EBreak

  | EContinue ->
      mk EContinue

  | ESequence _ ->
      failwith "[hoist_t]: sequences should've been translated as let _ ="

  | _ ->
      let lhs, e = hoist_expr loc Unspecified e in
      nest lhs e.typ e

(* This function returns an expression that can be successfully translated as a
 * C* expression. *)
and hoist_expr loc pos e =
  let mk node = { node; typ = e.typ; meta = e.meta } in
  match e.node with
  | ETApp (e, cgs, cgs', ts) ->
      let lhs, e = hoist_expr loc Unspecified e in
      lhs, mk (ETApp (e, cgs, cgs', ts))

  | EBufNull
  | EAbort _
  | EAny
  | EBound _
  | EOpen _
  | EQualified _
  | EConstant _
  | EUnit
  | EPushFrame | EPopFrame
  | EBool _
  | EString _
  | EEnum _
  | EStandaloneComment _
  | EPolyComp _
  | EOp _ ->
      [], e

  | EAddrOf e ->
      let lhs, e = hoist_expr loc Unspecified e in
      lhs, mk (EAddrOf e)

  | EIgnore e ->
      let lhs, e = hoist_expr loc Unspecified e in
      lhs, mk (EIgnore e)

  | EApp (e0, es) ->
      flag_short_circuit loc e.typ e0 es

  | ELet (binder, e1, e2) ->
      let lhs1, e1 = hoist_expr loc UnderStmtLet e1 in
      let binder, e2 = open_binder binder e2 in
      (* The caller (e.g. [hoist_t]) takes care, via [nest], of closing this
       * binder. *)
      let lhs2, e2 = hoist_expr loc pos e2 in
      lhs1 @ [ binder, e1 ] @ lhs2, e2

  | EIfThenElse (e1, e2, e3) ->
      let t = e.typ in
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      (* Doing the job of hoist_stmt here, so as to retain an accurate pos
       * instead of recursing back into hoist_expr with pos = Unspecified *)
      let lhs2, e2 = hoist_expr loc UnderConditional e2 in
      let e2 = nest lhs2 e2.typ e2 in
      let lhs3, e3 = hoist_expr loc UnderConditional e3 in
      let e3 = nest lhs3 e3.typ e3 in
      (* We now allow IfThenElse nodes directly under IfThenElse, on the basis
       * that the outer IfThenElse is properly positioned under a let-binding.
       * let_if_to_assign will know how to deal with this. *)
      if pos = UnderStmtLet || pos = UnderConditional then
        lhs1, mk (EIfThenElse (e1, e2, e3))
      else
        let b, body, cont = mk_named_binding "ite" t (EIfThenElse (e1, e2, e3)) in
        lhs1 @ [ b, body ], cont

  | EMatch (f, e, branches) ->
      (* Used only for the Rust backend -- we still want to hoist (it's good for
         code quality) but we disable data types compilation on the basis that
         Rust has proper data type support. *)
      let lhs, e = hoist_expr loc Unspecified e in
      let branches = List.map (fun (binders, p, e) ->
        let binders, e = open_binders binders e in
        let lhs, e = hoist_expr loc UnderConditional e in
        binders, p, close_binders binders (nest lhs e.typ e)
      ) branches in
      lhs, mk (EMatch (f, e, branches))

  | ESwitch (e1, branches) ->
      let t = e.typ in
      let lhs, e1 = hoist_expr loc Unspecified e1 in
      let branches = List.map (fun (tag, e) ->
        tag,
        let lhs, e = hoist_expr loc UnderConditional e in
        nest lhs e.typ e
      ) branches in
      if pos = UnderStmtLet || pos = UnderConditional then
        lhs, mk (ESwitch (e1, branches))
      else
        let b, body, cont = mk_named_binding "sw" t (ESwitch (e1, branches)) in
        lhs @ [ b, body ], cont

  | EWhile (e1, e2) ->
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      if lhs1 <> [] then
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc loc,
          GeneratesLetBindings ("this while loop's test expression", e, lhs1)));
      let e2 = hoist_stmt loc e2 in
      if pos = UnderStmtLet then
        [], mk (EWhile (e1, e2))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        [ b, mk (EWhile (e1, e2)) ], mk EUnit

  | EFor (binder, e1, e2, e3, e4) ->
      let lhs1, e1 = hoist_expr loc (if binder.node.meta = Some MetaSequence then UnderStmtLet else Unspecified) e1 in
      let binder, s = opening_binder binder in
      let e2 = s e2 and e3 = s e3 and e4 = s e4 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      let lhs3, e3 = hoist_expr loc UnderStmtLet e3 in
      (* Note: this should always be a fatal error when going to C, but only for
         the for-loop (since there is no workaround like for the if-then-else
         case. *)
      if lhs2 <> [] || lhs3 <> [] then
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc loc,
          GeneratesLetBindings ("this for-loop's condition or iteration", e, (lhs2 @ lhs3))));
      let e4 = hoist_stmt loc e4 in
      let s = closing_binder binder in
      (* If we get here let-bindings are ok for the chosen backend, likely wasm
         or rust *)
      if pos = UnderStmtLet then
        lhs1, mk (EFor (binder, e1, s (nest lhs2 e2.typ e2), s (nest lhs3 e3.typ e3), s e4))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs1 @ [ b, mk (EFor (binder, e1, s (nest lhs2 e2.typ e2), s (nest lhs3 e3.typ e3), s e4)) ], mk EUnit

  | EFun (binders, expr, t) ->
      let binders, expr = open_binders binders expr in
      let expr = hoist_stmt loc expr in
      let expr = close_binders binders expr in
      [], mk (EFun (binders, expr, t))

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      if pos = UnderStmtLet then
        lhs1 @ lhs2, mk (EAssign (e1, e2))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs1 @ lhs2 @ [ b, mk (EAssign (e1, e2)) ], mk EUnit

  | EBufCreate (l, e1, e2) ->
      let t = e.typ in
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = maybe_hoist_initializer loc (Helpers.assert_tbuf_or_tarray t) e2 in
      if pos = UnderStmtLet then
        lhs1 @ lhs2, mk (EBufCreate (l, e1, e2))
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreate (l, e1, e2)) in
        lhs1 @ lhs2 @ [ b, body ], cont

  | EBufCreateL (l, es) ->
      let t = e.typ in
      let lhs, es = List.split (List.map (maybe_hoist_initializer loc (Helpers.assert_tbuf_or_tarray t)) es) in
      let lhs = List.flatten lhs in
      if pos = UnderStmtLet then
        lhs, mk (EBufCreateL (l, es))
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreateL (l, es)) in
        lhs @ [ b, body ], cont

  | EBufRead (e1, e2) ->
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      lhs1 @ lhs2, mk (EBufRead (e1, e2))

  | EBufWrite (e1, e2, e3) ->
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      let lhs3, e3 = hoist_expr loc Unspecified e3 in
      let lhs = lhs1 @ lhs2 @ lhs3 in
      if pos = UnderStmtLet then
        lhs, mk (EBufWrite (e1, e2, e3))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufWrite (e1, e2, e3)) ], mk EUnit

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      let lhs3, e3 = hoist_expr loc Unspecified e3 in
      let lhs4, e4 = hoist_expr loc Unspecified e4 in
      let lhs5, e5 = hoist_expr loc Unspecified e5 in
      let lhs = lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5 in
      if pos = UnderStmtLet then
        lhs, mk (EBufBlit (e1, e2, e3, e4, e5))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufBlit (e1, e2, e3, e4, e5)) ], mk EUnit

  | EBufFill (e1, e2, e3) ->
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      let lhs3, e3 = hoist_expr loc Unspecified e3 in
      let lhs = lhs1 @ lhs2 @ lhs3 in
      if pos = UnderStmtLet then
        lhs, mk (EBufFill (e1, e2, e3))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufFill (e1, e2, e3)) ], mk EUnit

  | EBufFree e ->
      let lhs, e = hoist_expr loc Unspecified e in
      if pos = UnderStmtLet then
        lhs, mk (EBufFree e)
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufFree e) ], mk EUnit

  | EBufSub (e1, e2) ->
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      lhs1 @ lhs2, mk (EBufSub (e1, e2))

  | EBufDiff (e1, e2) ->
      let lhs1, e1 = hoist_expr loc Unspecified e1 in
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      lhs1 @ lhs2, mk (EBufDiff (e1, e2))

  | ECast (e, t) ->
      let lhs, e = hoist_expr loc Unspecified e in
      lhs, mk (ECast (e, t))

  | EField (e, f) ->
      let lhs, e = hoist_expr loc Unspecified e in
      lhs, mk (EField (e, f))

  | EFlat fields ->
      let lhs, fields = List.split (List.map (fun (ident, expr) ->
        let lhs, expr = hoist_expr loc Unspecified expr in
        lhs, (ident, expr)
      ) fields) in
      List.flatten lhs, mk (EFlat fields)

  | ECons (cons, fields) ->
      let lhs, fields = List.split (List.map (fun expr ->
        let lhs, expr = hoist_expr loc Unspecified expr in
        lhs, expr
      ) fields) in
      List.flatten lhs, mk (ECons (cons, fields))

  | ETuple es ->
      let lhs, es = List.split (List.map (hoist_expr loc Unspecified) es) in
      List.flatten lhs, mk (ETuple es)

  | ESequence _ ->
      fatal_error "[hoist_t]: sequences should've been translated as let _ ="

  | EReturn e ->
      if pos = UnderStmtLet || pos = UnderConditional then
        let lhs, e = hoist_expr loc Unspecified e in
        lhs, mk (EReturn e)
      else
        Warn.fatal_error "%a: %s" Loc.ploc loc "[return] expressions should only appear in statement position"

  | EBreak ->
      if pos = UnderStmtLet || pos = UnderConditional then
        [], mk EBreak
      else
        Warn.fatal_error "%a: %s" Loc.ploc loc "[break] expressions should only appear in statement position"

  | EContinue ->
      if pos = UnderStmtLet || pos = UnderConditional then
        [], mk EContinue
      else
        Warn.fatal_error "%a: %s" Loc.ploc loc "[continue] expressions should only appear in statement position"

(* TODO: figure out if we want to ignore the other cases for performance
 * reasons. *)
let hoist = object
  inherit [_] map as super

  method! visit_file loc file =
    super#visit_file Loc.(File (fst file) :: loc) file

  method! visit_DFunction loc cc flags n_cgs n ret name binders expr =
    let loc = Loc.(InTop name :: loc) in
    (* TODO: no nested let-bindings in top-level value declarations either *)
    let binders, expr = open_binders binders expr in
    let expr = hoist_stmt loc expr in
    let expr = close_binders binders expr in
    DFunction (cc, flags, n_cgs, n, ret, name, binders, expr)
end


(* Relax the criterion a little bit for terminal positions ********************)

let rec fixup_return_pos e =
  (* We know how to insert returns and won't need assignments for things that
   * are in terminal position. To keep in sync with [AstToCStar.extract_stmts]
   * and [AstToCStar.translate_function_block]. This transforms:
   *   let x = if ... then ... else in
   *   x
   * into:
   *   if .. then ... else
   * because it's valid for if nodes to appear in terminal position (idem for
   * switch nodes).
   * *)
  { e with node = match e.node with
    | ELet (_, ({ node = (EIfThenElse _ | ESwitch _ | EMatch _); _ } as e), { node = EBound 0; _ }) ->
        (fixup_return_pos e).node
    | ELet (_, ({ node = (EIfThenElse _ | ESwitch _ | EMatch _); _ } as e),
      { node = ECast ({ node = EBound 0; _ }, t); _ }) ->
        (nest_in_return_pos t (fun _ e -> with_type t (ECast (e, t))) (fixup_return_pos e)).node
    | EIfThenElse (e1, e2, e3) ->
        EIfThenElse (e1, fixup_return_pos e2, fixup_return_pos e3)
    | ESwitch (e1, branches) ->
        ESwitch (e1, List.map (fun (t, e) -> t, fixup_return_pos e) branches)
    | EMatch (f, e1, branches) ->
        EMatch (f, e1, List.map (fun (bs, pat, e) -> bs, pat, fixup_return_pos e) branches)
    | ELet (b, e1, e2) ->
        ELet (b, e1, fixup_return_pos e2)
    | e ->
        e
  }

(* TODO: figure out if we want to ignore the other cases for performance
 * reasons. *)
let fixup_hoist = object
  inherit [_] map

  method visit_DFunction _ cc flags n_cgs n ret name binders expr =
    DFunction (cc, flags, n_cgs, n, ret, name, binders, fixup_return_pos expr)
end



(* Make top-level names C-compatible using a global translation table **********)

(* A reverse map whose domain is all the top-level declarations that end up
 * in a .h file. Notably, private functions are absent from the map. *)
let original_of_c_name: (ident, lident) Hashtbl.t = Hashtbl.create 43

type scope_env = GlobalNames.t * (string, GlobalNames.t) Hashtbl.t

class scope_helpers = object (self)
  val mutable current_file = ""

  method private is_private_scope flags lident =
    List.mem Common.Private flags && not (Helpers.is_static_header lident)

  method private record (global_scope, local_scopes) ~is_type ~is_external flags lident =
    let kind =
      if is_type then
        GlobalNames.Type
      else if List.mem Common.Macro flags || List.mem Common.IfDef flags then
        Macro
      else
        Other
    in
    let is_private = self#is_private_scope flags lident in
    let local_scope = Hashtbl.find local_scopes current_file in
    let attempt_shortening = is_private && not is_external in
    let target = GlobalNames.target_c_name ~attempt_shortening ~kind lident in
    (* KPrint.bprintf "%a --> %s\n" plid lident (fst target); *)
    let c_name = GlobalNames.extend global_scope local_scope is_private lident target in
    if not is_private then
      Hashtbl.add original_of_c_name c_name lident
end

let record_toplevel_names = object (self)
  inherit [_] iter as super
  inherit scope_helpers

  (* Every file gets a fresh local scope. This is after bundling. *)
  method! visit_file (env: scope_env) f =
    let global_scope, local_scopes = env in
    current_file <- fst f;
    Hashtbl.add local_scopes (fst f) (GlobalNames.clone global_scope);
    super#visit_file env f

  (* We record the names of all top-level declarations. *)
  method! visit_DGlobal env flags name _ _ _ =
    self#record env ~is_type:false ~is_external:false flags name

  method! visit_DFunction env _ flags _ _ _ name _ _ =
    self#record env ~is_type:false ~is_external:false flags name

  method! visit_DExternal env _ flags _ _ name _ _ =
    self#record env ~is_type:false ~is_external:true flags name

  val forward = Hashtbl.create 41

  method! visit_DType env name flags _ _ def =
    if not (Hashtbl.mem forward name) then
      self#record env ~is_type:true ~is_external:false flags name;
    match def with
    | Enum lids -> List.iter (fun (lid, _) -> self#record env ~is_type:true ~is_external:false flags lid) lids
    | Forward _ -> Hashtbl.add forward name ()
    | _ -> ()
end


(* Compile tail-calls into loops *********************************************)

(** Essentially:
  *
  *                               let f x0 y0 =
  * let f x y =                     let x = x0 and y = y0 in
  *   if ... then        ----->     while true
  *     f e1 e2                       if ... then
  *   else                              x <- e1; y <- e2
  *     e3                            else
  *                                     return e3
  *                                 failwith "unreachable"
  *)

let tail_calls =
  let module T = struct
    exception NotTailCall
    exception NothingToTailCall
  end in

  (* Transform an expression into a unit assignment to either the mutable
   * parameters, or the destination. *)
  let make_tail_calls lid a_args e =

    let fail_if_self_call = (object
      inherit [_] iter
      method! visit_EQualified _ lid' =
        if lid = lid' then
          raise T.NotTailCall
    end)#visit_expr_w () in

    let found = ref false in

    let rec make_tail_calls e =
      with_unit (match e.node with
        | EMatch _ ->
            failwith "must run after pattern match compilation"

        | ELet (b, e1, e2) ->
            fail_if_self_call e1;
            ELet (b, e1, make_tail_calls e2)

        | ESwitch (e, branches) ->
            fail_if_self_call e;
            ESwitch (e, List.map (fun (case, e) -> case, make_tail_calls e) branches)

        | EIfThenElse (e1, e2, e3) ->
            fail_if_self_call e1;
            EIfThenElse (e1, make_tail_calls e2, make_tail_calls e3)

        | EApp ({ node = EQualified lid'; _ }, args) when lid' = lid ->
            found := true;
            (* Implement a capture-avoiding substitution by first assigning in a
               set of temporaries, then assigning the temporaries back into the
               mutable arguments. We could reuse the function arguments for
               that, but I thought it'd be cleaner to have a set of variables
               named `tmp` whose purpose is 100% clear. *)
            let replacements = KList.filter_some (List.map2 (fun x arg ->
              (* Don't generate x = x as this is oftentimes a fatal warning. *)
              if x = arg then
                None
              else
                let tmp_arg_b, tmp_arg_ref =
                  Helpers.mk_binding ~mut:true "tmp" arg.typ
                in
                Some ((tmp_arg_b, arg), with_unit (EAssign (x, tmp_arg_ref)))
            ) a_args args) in
            if replacements = [] then
              EUnit
            else
              let tmp_args, assignments = List.split replacements in
              (List.fold_right (fun (b, def) arg ->
                with_unit (ELet (b, def, close_binder b arg))
              ) tmp_args (with_unit (ESequence assignments))).node

        | ESequence es ->
            let es, last = KList.split_at_last es in
            List.iter fail_if_self_call es;
            ESequence (es @ [ make_tail_calls last ])

        | _ ->
            fail_if_self_call e;
            EReturn e
      )
    in

    let e = make_tail_calls e in
    if not !found then
      raise T.NothingToTailCall;
    e
  in

  let tail_calls = object (_)
    inherit [_] map

    method! visit_DFunction () cc flags n_cgs n ret name binders body =
      try
        let x_args = List.map (fun b -> Helpers.fresh_binder ~mut:true b.node.name b.typ) binders in
        let x_args, body = DeBruijn.open_binders x_args body in
        let a_args = List.map DeBruijn.term_of_binder x_args in
        let binders = List.map (fun b ->
          { b with node = { b.node with name = b.node.name ^ "0" } }) binders
        in
        let l = List.length x_args in
        let state = List.mapi (fun i b -> b, with_type b.typ (EBound (l - 1 - i))) x_args in
        let body =
          nest state ret (with_type ret (ESequence [
            with_unit (EWhile (etrue, make_tail_calls name a_args body));
            with_type ret (EAbort (None, Some "unreachable, returns inserted above"))
          ]))
        in
        DFunction (cc, flags, n_cgs, n, ret, name, binders, body)
      with
      | T.NotTailCall ->
          Warn.(maybe_fatal_error ("", NotTailCall name));
          DFunction (cc, flags, n_cgs, n, ret, name, binders, body)
      | T.NothingToTailCall ->
          DFunction (cc, flags, n_cgs, n, ret, name, binders, body)
  end in

  tail_calls#visit_files ()


(* Extend the lifetimes of buffers ********************************************)

(** This function hoists let-buffers up to the nearest enclosing push_frame so
 * that their lifetime is not shortened by an upcoming C braced block.
 *
 * Consider:
 *   push_frame ();
 *   let b = if true then let b1 = bufcreatel ... in subbuf b1 0 else ... in
 *
 * This is fine per the C* semantics but not safe to transform "as is" into: {[
 *   int* b;
 *   if true then {
 *     int b1[] = { 1, 2, 3, 4, 5 };
 *     b = b1;
 *   }
 * ]}
 *
 * This function rewrites the snippet above into:
 *   push_frame ();
 *   let b1: array int 5 = any;
 *   let b = if true then copy-assign (b1, bufcreatel ...); subbuf b1 0 else ...
 *
 * This relies on a helper to create copy-assignments.
 *
 * This function assumes [hoist] has been run so that every single [EBufCreate]
 * appears as a [let x = bufcreate...], always in statement position.
 *)
let rec hoist_bufcreate ifdefs (e: expr) =
  let hoist_bufcreate = hoist_bufcreate ifdefs in
  let under_pushframe = under_pushframe ifdefs in
  let mk node = { node; typ = e.typ; meta = e.meta } in
  match e.node with
  | EMatch _ ->
      failwith "expected to run after match compilation"

  | EIfThenElse (e1, e2, e3) ->
      let b2, e2 = hoist_bufcreate e2 in
      let b3, e3 = hoist_bufcreate e3 in
      b2 @ b3, mk (EIfThenElse (e1, e2, e3))

  | ESwitch (e, branches) ->
      let bs, branches = List.fold_left (fun (bss, branches) (t, e) ->
        let bs, e = hoist_bufcreate e in
        bs @ bss, (t, e) :: branches
      ) ([], []) branches in
      let bs = List.rev bs in
      let branches = List.rev branches in
      bs, mk (ESwitch (e, branches))

  | EWhile (e1, e2) ->
      let bs, e2 = hoist_bufcreate e2 in
      bs, mk (EWhile (e1, e2))

  | ELet (b, ({ node = EPushFrame; _ } as e1), e2) ->
      [], mk (ELet (b, e1, under_pushframe e2))

  | ELet (b, e1, e2) ->
      (* Either:
       *   [let x: t* = bufcreatel ...] (as-is in the original code)
       *   [let x: t[n] = any] (because C89 hoisting kicked in).
       * Instead of using an encoding of copy-assignments, we actually generate
       * proper instructions now. *)
      begin match strengthen_array b.typ e1 with
      | TArray (t, size) as tarray ->
          (* b is the binder that is about to be moved up *)
          let b, e2 = open_binder b e2 in
          (* Any assignments into b will be desugared as a
           * copy-assignment, thanks to the strengthened type. *)
          let b = { b with typ = tarray } in
          let bs, e2 = hoist_bufcreate e2 in
          (* WASM/C discrepancy; in C, the array type makes sure we allocate
           * stack space. In Wasm, we rely on the expression to actually
           * generate run-time code. *)
          let init e = with_type (TBuf (t, false)) (
            EBufCreate (Common.Stack, e, with_type uint32 (EConstant size)))
          in
          begin match e1.node with
          | EAny ->
              failwith "not allowing that per WASM restrictions"
          | EBufCreate (_, e, _) when Helpers.is_closed_term e ->
              (b, init e) :: bs, e2
          | EBufCreate (_, { node = EAny; _ }, _) ->
              (* We're visiting this node again. *)
              (mark_mut b, init any) :: bs, e2
          | _ ->
              (* Need actual copy-assigment. *)
              (mark_mut b, init any) :: bs,
              mk (ELet (sequence_binding (),
                with_type TUnit (mk_copy_assignment (t, size) (EOpen (b.node.name, b.node.atom)) e1),
                lift 1 e2
              ))
          end
      | _ ->
          let b1, e1 = hoist_bufcreate e1 in
          let b2, e2 = hoist_bufcreate e2 in
          b1 @ b2, mk (ELet (b, e1, e2))
      end

  | _ ->
      [], e

(* TODO: the control-flow is super convoluted here. Also, why the difference in
   treatment between while loops and for loops above? Is this some ancient
   Dafny-related stuff? In any case, I believe the two mutually-recursive
   functions could be greatly clarified if they operated at the level of lets
   instead of alternating between the sequence of statements (all lets) and the
   bodies of the lets themselves. *)
and under_pushframe ifdefs (e: expr) =
  let hoist_bufcreate = hoist_bufcreate ifdefs in
  let under_pushframe = under_pushframe ifdefs in
  let mk node = { node; typ = e.typ; meta = e.meta } in
  match e.node with
  | ELet (b, { node = EIfThenElse ({ node = EQualified lid; _ } as e1, e2, e3); typ; meta = [] }, ek)
    when Idents.LidSet.mem lid ifdefs ->
      (* Do not hoist, since this if will turn into an ifdef which does NOT
         shorten the scope...! TODO this does not catch all ifdefs *)
      let e2 = under_pushframe e2 in
      let e3 = under_pushframe e3 in
      let ek = under_pushframe ek in
      mk (ELet (b, { node = EIfThenElse (e1, e2, e3); typ; meta = [] }, ek))
  | ELet (b, e1, e2) ->
      let b1, e1 = hoist_bufcreate e1 in
      let e2 = under_pushframe e2 in
      nest b1 e.typ (mk (ELet (b, e1, e2)))
  | EIfThenElse ({ node = EQualified lid; _ } as e1, e2, e3)
    when Idents.LidSet.mem lid ifdefs ->
      let e2 = under_pushframe e2 in
      let e3 = under_pushframe e3 in
      mk (EIfThenElse (e1, e2, e3))
  | _ ->
      let b, e' = hoist_bufcreate e in
      nest b e.typ e'

(* This function skips the first few statements until we hit the first
 * push_frame, and then starts hoisting. The reason for that is:
 * - either whatever happens before push is benign
 * - or, something happens (e.g. allocation), and this means that the function
 *   WILL be inlined, and that its caller will take care of hoisting things up
 *   in the second round.
 *
 * JP, 20220810: the second case above seems EXTREMELY outdated, since now all
 * StackInline functions are also marked as inline_for_extraction.
 *
 * Note: we could do this in a simpler manner with a visitor whose env is a
 * [ref * (list (binder * expr))] but that would degrade the quality of the
 * code. This recursive routine is smarter and preserves the sequence of
 * let-bindings starting from the beginning of the scope. *)
let rec find_pushframe ifdefs (e: expr) =
  let mk node = { node; typ = e.typ; meta = e.meta } in
  match e.node with
  | ELet (b, ({ node = EPushFrame; _ } as e1), e2) ->
      mk (ELet (b, e1, under_pushframe ifdefs e2))
  | ELet (b, e1, e2) ->
      (* No need to descend into `e1` since we won't find let bindings there. *)
      mk (ELet (b, e1, find_pushframe ifdefs e2))
  (* Descend into conditionals that are in return position. *)
  | EIfThenElse (e1, e2, e3) ->
      mk (EIfThenElse (e1, find_pushframe ifdefs e2, find_pushframe ifdefs e3))
  | ESwitch (e, branches) ->
      mk (ESwitch (e, List.map (fun (t, e) -> t, find_pushframe ifdefs e) branches))
  | EMatch (f, e, branches) ->
      mk (EMatch (f, e, List.map (fun (t, p, e) -> t, p, find_pushframe ifdefs e) branches))
  | _ ->
      e

(* This phase operates after `hoist` and `let_if_to_assign`, meaning we can rely
  on a few invariants:
  - let-bindings do not nest right
  - buffer allocations are always immediately underneath a let-bindings
  - ifs are in statement position
  - there are no sequences, but unit let-bindings. *)
let hoist_bufcreate = object
  inherit [_] map

  method visit_DFunction ifdefs cc flags n_cgs n ret name binders expr =
    try
      DFunction (cc, flags, n_cgs, n, ret, name, binders, find_pushframe ifdefs expr)
    with Fatal s ->
      KPrint.bprintf "Fatal error in %a:\n%s\n" plid name s;
      exit 151
end

(* Dealing with local functions ***********************************************)

(* TODO: this should ABSOLUTELY be implemented at the F* level -- it's
 * ridiculous to have that sort of normalization steps happen here. *)
let remove_local_function_bindings = object(self)

  inherit [_] map

  method! visit_ELet env b e1 e2 =
    let e1 = self#visit_expr env e1 in
    match e1.node with
    | ECast ({ node = EFun _; _ } as e1, _) ->
        let e2 = DeBruijn.subst e1 0 e2 in
        (self#visit_expr env e2).node
    | EFun _ ->
        let e2 = DeBruijn.subst e1 0 e2 in
        (self#visit_expr env e2).node
    | _ ->
        let e2 = self#visit_expr env e2 in
        ELet (b, e1, e2)

  method! visit_EApp (env, t) e es =
    let e = self#visit_expr_w env e in
    let es = List.map (self#visit_expr_w env) es in
    match e.node with
    | EFun (_, body, _) ->
        (safe_substitution es body t).node
    | _ ->
        EApp (e, es)
end

(* Combinators ****************************************************************)

(* This needs to happen after local function bindings have been substituted. *)
let combinators = object(self)

  inherit [_] map as super

  method private mk_for start finish body w =
    let b = fresh_binder "i" (TInt w) in
    let b = mark_mut b in
    let cond = mk_lt w (lift 1 finish) in
    let iter = mk_incr w in
    (* Note: no need to shift, the body was under a one-argument lambda
     * already. *)
    EFor (b, start, cond, iter, self#visit_expr_w () body)

  method! visit_EApp (_, t) e es =

    let mk_app t f x =
      match f with
      | { node = EFun (_, body, _); _ } ->
         DeBruijn.subst x 0 body
      | _ ->
         with_type t (EApp (f, [x]))
    in

    match e.node, es with
    | EQualified ("C" :: (["Loops"]|["Compat";"Loops"]), "for64"), [ start; finish; _inv; { node = EFun (_, body, _); _ } ] ->
        self#mk_for start finish body K.UInt64

    | EQualified ("C" :: (["Loops"]|["Compat";"Loops"]), s), [ start; finish; _inv; { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "for" ->
        self#mk_for start finish body K.UInt32

    | EQualified (["Steel"; "ST"; "Loops"], s), [ start; finish; _inv; { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "for_loop" ->
        self#mk_for start finish body K.SizeT

    | EQualified (["Steel"; "Loops"], s), [ start; finish; _inv; { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "for_loop" ->
        self#mk_for start finish body K.SizeT

    | EQualified ("C" :: (["Loops"]|["Compat";"Loops"]), s), [ _measure; _inv; tcontinue; body; init ]
        when KString.starts_with s "total_while_gen"
       ->
        let b = fresh_binder "b" TBool in
        let b = mark_mut b in
        let x = fresh_binder "x" t in
        let x = mark_mut x in
        (* Binder 1 *)
        ELet (b, etrue, with_type t (
        (* Binder 0 *)
        ELet (x, lift 1 init, with_type t (
        ESequence [
          with_unit (EWhile (
            with_type TBool (EBound 1),
            with_unit (ESequence [
              with_unit (EAssign (
                with_type t (EBound 0),
                mk_app t (lift 2 (self#visit_expr_w () body)) (with_type t (EBound 0))
              ));
              with_unit (EAssign (
                with_type TBool (EBound 1),
                mk_app t (lift 2 tcontinue) (with_type t (EBound 0))
              ));
           ])
          ));
          with_type t (EBound 0);
        ]))))

    | EQualified ("C" :: (["Loops"]|["Compat";"Loops"]), "interruptible_for"), [ start; finish; _inv; { node = EFun (_, _, _); _ } as f ] ->
        (* Relying on the invariant that, if [finish] is effectful, F* has
         * hoisted it *)
        assert (is_value finish);
        let b = fresh_binder "b" TBool in
        let b = mark_mut b in
        let i = fresh_binder "i" uint32 in
        let i = mark_mut i in
        let iter = mk_incr32 in
        (* First binder. *)
        ELet (b, efalse, with_type t (
        (* Second binder. *)
        ELet (i, lift 1 start, with_type t (
        ESequence [
          with_type TUnit (EFor (
            (* Third binder. *)
            Helpers.unused_binding (),
            any,
            mk_and
              (mk_not (with_type TBool (EBound 2)))
              (mk_neq (with_type uint32 (EBound 1)) (lift 3 finish)),
            lift 1 iter,
            with_unit (EAssign
              (with_type TBool (EBound 2),
              self#visit_expr_w () (
                let f = lift 3 f in
                let body = match f with
                  | { node = EFun  (_, body, _); _ } -> body
                  | _ -> assert false
                in
                DeBruijn.subst (with_type uint32 (EBound 1)) 0 body
                )))));
          with_type t (ETuple [
            with_type uint32 (EBound 0);
            with_type TBool (EBound 1)])]))))

    | EQualified ("C" :: (["Loops"]|["Compat";"Loops"]), s), [
        { node = EFun (_, test, _); _ };
        { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "while" ->
        EWhile (DeBruijn.subst Helpers.eunit 0 (self#visit_expr_w () test),
          DeBruijn.subst Helpers.eunit 0 (self#visit_expr_w () body))

    | EQualified (["Steel"; "ST"; "Loops"], s), [ _inv;
        { node = EFun (_, test, _); _ };
        { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "while_loop" ->
        EWhile (DeBruijn.subst Helpers.eunit 0 (self#visit_expr_w () test),
          DeBruijn.subst Helpers.eunit 0 (self#visit_expr_w () body))

    | EQualified (["Steel"; "Loops"], s), [ _inv;
        { node = EFun (_, test, _); _ };
        { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "while_loop" ->
        EWhile (DeBruijn.subst Helpers.eunit 0 (self#visit_expr_w () test),
          DeBruijn.subst Helpers.eunit 0 (self#visit_expr_w () body))

    | EQualified ("C" :: (["Loops"]|["Compat";"Loops"]), s), [ { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "do_while" ->
        EWhile (etrue, with_unit (
          EIfThenElse (DeBruijn.subst eunit 0 (self#visit_expr_w () body),
            with_unit EBreak,
            eunit)))

    | _ ->
        super#visit_EApp ((), t) e es

end

let fixup_while_tests = object (self)

  inherit [_] map as super

  method! visit_EWhile (_, t) cond body =
    match cond.node with
    (* TODO: Helpers.unlikely_expression *)
    | ELet _
    | EIfThenElse _ ->
        let body = self#visit_expr_w () body in
        let cond = self#visit_expr_w () cond in

        let b_cond, def_cond, _ =
          mk_named_binding "cond" cond.typ cond.node
        in
        let b_cond = mark_mut b_cond in

        (* let cond = <cond> in *)
        ELet (b_cond, def_cond,
          (* while (cond) { *)
          with_type t (EWhile (with_type cond.typ (EBound 0),
            (* let _ = <body> in *)
            with_type body.typ (ELet (sequence_binding (),
              DeBruijn.lift 1 body,
              (* cond <- <cond> *)
              with_unit (EAssign (with_type cond.typ (EBound 1), DeBruijn.lift 2 def_cond)))))))

    | _ ->
        super#visit_EWhile ((), t) cond body

end



(* The various series of rewritings called by Karamel.ml **********************)

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

(* Macros that may generate tuples and sequences. Run before data types
 * compilation, once. *)
let simplify0 (files: file list): file list =
  let files = remove_local_function_bindings#visit_files () files in
  let files = optimize_lets files in
  let files = remove_ignore_unit#visit_files () files in
  let files = remove_proj_is#visit_files () files in
  let files = combinators#visit_files () files in
  let files = wrapping_arithmetic#visit_files () files in
  files

(* This removes superfluous units. Useful for top-level constants that may have
 * calls of the form recall foobar in them. *)
let simplify1 (files: file list): file list =
  let files = sequence_to_let#visit_files () files in
  let files = optimize_lets files in
  let files = let_to_sequence#visit_files () files in
  files

(* This should be run late since inlining may create more opportunities for the
 * removal of unused variables. *)
let remove_unused (files: file list): file list =
  (* Relying on the side-effect of refreshing the mark. *)
  let files = optimize_lets files in
  let parameter_table = Hashtbl.create 41 in
  unused_parameter_table#visit_files parameter_table files;
  ignore_non_first_order#visit_files parameter_table files;
  let files = remove_unused_parameters#visit_files (parameter_table, 0) files in
  files

(* Many phases rely on a statement-like language where let-bindings, buffer
 * allocations and writes are hoisted; where if-then-else is always in statement
 * position; where sequences are not nested. These series of transformations
 * re-establish this invariant. *)
let simplify2 ifdefs (files: file list): file list =
  let files = sequence_to_let#visit_files () files in
  (* Quality of hoisting is WIDELY improved if we remove un-necessary
   * let-bindings. Also removes occurrences of spinlock and the like. *)
  let files = optimize_lets ~ifdefs files in
  let files = if Options.wasm () then files else fixup_while_tests#visit_files () files in
  let files = hoist#visit_files [] files in
  let files = if !Options.c89_scope then SimplifyC89.hoist_lets#visit_files (ref []) files else files in
  let files = if Options.wasm () then files else fixup_hoist#visit_files () files in
  (* Disabled in Rust because this results in uninitialized variables *)
  let files = if Options.wasm () || Options.rust () then files else let_if_to_assign#visit_files () files in
  (* NB: could be disabled for Rust since the Rust checker will error out *)
  let files = if Options.wasm () then files else hoist_bufcreate#visit_files ifdefs files in
  (* This phase relies on up-to-date mark information. TODO move up after
     optimize_lets. *)
  let files = misc_cosmetic#visit_files () files in
  let files = misc_cosmetic2#visit_files () files in
  let files = functional_updates#visit_files false files in
  let files = functional_updates#visit_files true files in
  let files = let_to_sequence#visit_files () files in
  files

let debug env =
  KPrint.bprintf "Global scope:\n";
  GlobalNames.dump (fst env);
  KPrint.bprintf "\n\n";
  Hashtbl.iter (fun f s ->
    KPrint.bprintf "%s scope:\n" f;
    GlobalNames.dump s;
    KPrint.bprintf "\n\n"
  ) (snd env);
  KPrint.bprintf "Reverse-map:\n";
  Hashtbl.iter (fun c_name original ->
    KPrint.bprintf "C name %s was %a\n" c_name plid original
  ) original_of_c_name

(* Returns the internal env for further name extension. *)
let allocate_c_env (files: file list): scope_env =
  let env = GlobalNames.create (), Hashtbl.create 41 in
  record_toplevel_names#visit_files env files;
  if Options.debug "c-names" then
    debug env;
  env

(* Allocate C names avoiding keywords and name collisions. Mapping cannot be extended any further
   since the internal data structures are gone. *)
let allocate_c_names (files: file list): GlobalNames.mapping =
  GlobalNames.mapping (fst (allocate_c_env files))
