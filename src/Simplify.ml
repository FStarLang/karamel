(** This module rewrites the original AST to send it into Low*, the subset we
 * know how to translate to C. *)

open Ast
open DeBruijn
open Idents
open Warnings
open PrintAst.Ops
open Helpers


(* Count the number of occurrences of each variable ***************************)

let count_and_remove_locals = object (self)

  inherit [_] map

  method! extend env binder =
    binder.node.mark := 0;
    binder :: env

  method! visit_EBound (env, _) i =
    let b = List.nth env i in
    incr b.node.mark;
    EBound i

  method! visit_ELet (env, _) b e1 e2 =
    (* Remove unused variables. Important to get rid of calls to [HST.get()]. *)
    let e1 = self#visit_expr_w env e1 in
    let env = self#extend env b in
    let e2 = self#visit_expr_w env e2 in
    if !(b.node.mark) = 0 && is_readonly_c_expression e1 then
      (snd (open_binder b e2)).node
    else if !(b.node.mark) = 0 then
      if e1.typ = TUnit then
        ELet ({ b with node = { b.node with meta = Some MetaSequence }}, e1, e2)
      else
        (* We know the variable is unused... but its body cannot be determined
         * to be readonly, so we have to keep. What's better?
         *   int unused = f();
         * or:
         *   (void)f(); ? *)
        (* ELet ({ node = { b.node with meta = Some MetaSequence }; typ = TUnit}, push_ignore e1, e2) *)
        ELet (b, e1, e2)
    else
      ELet (b, e1, e2)

  method! visit_EBufSub env e1 e2 =
    (* This creates more opportunities for values to be eliminated if unused.
     * Also, AstToCStar emits BufSub (e, 0) as just e, so we need the value
     * check to be in agreement on both sides. *)
    match e2.node with
    | EConstant (_, "0") ->
        (self#visit_expr env e1).node
    | _ ->
        EBufSub (self#visit_expr env e1, self#visit_expr env e2)

end

let implies x y =
  not x || y

let unused_typ typs i =
  let t = List.nth typs i in
  let unused t = t = TUnit in
  (* The first typ may be marked as unused only if there's another unused
   * typ later on, otherwise, it serves at the one remaining typ that
   * makes sure this is still a function, and not a computation. *)
  unused t &&
  implies (i = 0) (List.exists (fun t -> not (unused t)) (List.tl typs))

let unused_binder binders i =
  unused_typ (List.map (fun b -> b.typ) binders) i

(* To be run immediately after the phase above. *)
let build_unused_map map = object
  inherit [_] iter

  method! visit_DFunction _ _ _ _ _ name binders _ =
    Hashtbl.add map name (KList.make (List.length binders) (unused_binder binders))

  method! visit_DExternal _ _ _ name t =
    match t with
    | TArrow _ ->
        let _, args = flatten_arrow t in
        Hashtbl.add map name (KList.make (List.length args) (unused_typ args))
    | _ ->
        ()
end

(* Ibid. *)
let remove_unused_parameters map = object (self)
  inherit [_] map

  method! visit_DFunction env cc flags n ret name binders body =
    let n_binders = List.length binders in
    let body = List.fold_left (fun body i ->
      if unused_binder binders i then
        DeBruijn.subst eunit (n_binders - 1 - i) body
      else
        body
    ) body (KList.make n_binders (fun i -> i)) in
    let body = self#visit_expr_w env body in
    let unused = KList.make (List.length binders) (fun i -> not (unused_binder binders i)) in
    let binders = KList.filter_mask unused binders in
    DFunction (cc, flags, n, ret, name, binders, body)

  method! visit_DExternal _ cc flags name t =
    let t =
      match t with
      | TArrow _ ->
          let ret, args = flatten_arrow t in
          let unused = KList.make (List.length args) (fun i -> not (unused_typ args i)) in
          let args = KList.filter_mask unused args in
          fold_arrow args ret
      | _ ->
          t
    in
    DExternal (cc, flags, name, t)

  method! visit_EApp (env, t) e es =
    let es = List.map (self#visit_expr_w env) es in
    match e.node with
    | EQualified lid when
      Hashtbl.mem map lid &&
      List.length (Hashtbl.find map lid) = List.length (snd (flatten_arrow e.typ)) ->
        let e =
          let t, ts = flatten_arrow e.typ in
          let ts = KList.filter_mask (List.map not (Hashtbl.find map lid)) ts in
          { e with typ = fold_arrow ts t }
        in
        (* There are some partial applications lurking around in spec... Checker
         * should really remove these. *)
        let are_unused, _ = KList.split (List.length es) (Hashtbl.find map lid) in
        let es, to_evaluate = List.fold_left2 (fun (es, to_evaluate) unused arg ->
          if unused then
            if is_readonly_c_expression arg then
              es, to_evaluate
            else
              let x, _atom = mk_binding "unused" arg.typ in
              es, (x, arg) :: to_evaluate
          else
            arg :: es, to_evaluate
        ) ([], []) are_unused es in
        let es = List.rev es in
        let to_evaluate = List.rev to_evaluate in
        (nest to_evaluate t (with_type t (EApp (e, es)))).node

    | _ ->
        EApp (self#visit_expr_w env e, es)
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
        let c e = { node = ECast (e, TInt unsigned_w); typ = TInt unsigned_w } in
        (** TODO: the second call to [c] is optional per the C semantics, but in
         * order to preserve typing, we have to insert it... maybe recognize
         * that pattern later on at the C emission level? *)
        let unsigned_app = { node = EApp (e, [ c e1; c e2 ]); typ = TInt unsigned_w } in
        ECast (unsigned_app, TInt w)

    | EOp (((K.AddW | K.SubW | K.MultW | K.DivW) as op), w), [ e1; e2 ] when K.is_unsigned w ->
        let e = mk_op (K.without_wrap op) w in
        let e1 = self#visit_expr env e1 in
        let e2 = self#visit_expr env e2 in
        EApp (e, [ e1; e2 ])

    | _, es ->
        EApp (self#visit_expr env e, List.map (self#visit_expr env) es)
end


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
   * don't care what happens in [e2]), otherwise, just a regular composition. *)
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
  method! visit_EAssign env e1 e2 = self#unordered env [ e1; e2 ]
  method! visit_EApp env e es =
    match e.node with
    | EOp _ -> super#visit_EApp env e es
    | EQualified lid when Helpers.is_readonly_builtin_lid lid -> super#visit_EApp env e es
    | _ -> self#unordered env (e :: es)

  method! visit_ELet env _ e1 e2 = self#sequential env e1 (Some e2)
  method! visit_EIfThenElse env e _ _ = self#sequential env e None
  method! visit_ESwitch env e _ = self#sequential env e None
  method! visit_EWhile env e _ = self#sequential env e None
  method! visit_EFor env _ e _ _ _ = self#sequential env e None
  method! visit_EMatch env e _ = self#sequential env e None
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

(* Try to remove the infamous let uu____ from F*. Needs an accurate use count
 * for each variable. *)
let remove_uu = object (self)

  inherit [_] map

  method! visit_ELet _ b e1 e2 =
    let e1 = self#visit_expr_w () e1 in
    let e2 = self#visit_expr_w () e2 in
    if KString.starts_with b.node.name "uu___" &&
      !(b.node.mark) = 1 && (
        is_readonly_c_expression e1 &&
        safe_readonly_use e2 ||
        safe_pure_use e2
      )
    then
      (DeBruijn.subst e1 0 e2).node
    else
      ELet (b, e1, e2)
end


(* Convert back and forth between [e1; e2] and [let _ = e1 in e2]. ************)

let sequence_to_let = object (self)

  inherit [_] map

  method! visit_ESequence env es =
    let es = List.map (self#visit_expr env) es in
    match List.rev es with
    | last :: first_fews ->
        (List.fold_left (fun cont e ->
          { node = ELet (sequence_binding (), e, lift 1 cont); typ = last.typ }
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
      typ = TUnit
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

let misc_cosmetic = object (self)

  inherit [_] map

  method! visit_EIfThenElse env e1 e2 e3 =
    let e1 = self#visit_expr env e1 in
    let e2 = self#visit_expr env e2 in
    let e3 = self#visit_expr env e3 in
    match e2.node with
    | EUnit when e3.node <> EUnit ->
        EIfThenElse (Helpers.mk_not e1, e3, e2)
    | _ ->
        EIfThenElse (e1, e2, e3)

  method visit_EAddrOf env e =
    let e = self#visit_expr env e in
    match e.node with
    | EBufRead (e, { node = EConstant (_, "0"); _ }) ->
        e.node
    | _ ->
        EAddrOf e

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
  | AssignRhs
  | Unspecified
  | BufAssignee

let rec hoist_stmt e =
  let mk node = { node; typ = e.typ } in
  match e.node with
  | EApp (e, es) ->
      (* A call is allowed in terminal position regardless of whether it has
       * type unit (generates a statement) or not (generates a [EReturn expr]). *)
      let lhs, e = hoist_expr Unspecified e in
      let lhss, es = List.split (List.map (hoist_expr Unspecified) es) in
      let lhs = lhs @ List.flatten lhss in
      nest lhs e.typ (mk (EApp (e, es)))

  | ELet (binder, e1, e2) ->
      (* When building a statement, let-bindings may nest right but not left. *)
      let lhs, e1 = hoist_expr UnderStmtLet e1 in
      let binder, e2 = open_binder binder e2 in
      let e2 = hoist_stmt e2 in
      nest lhs e.typ (mk (ELet (binder, e1, close_binder binder e2)))

  | EIfThenElse (e1, e2, e3) ->
      if e.typ = TUnit then
        let lhs, e1 = hoist_expr Unspecified e1 in
        let e2 = hoist_stmt e2 in
        let e3 = hoist_stmt e3 in
        nest lhs e.typ (mk (EIfThenElse (e1, e2, e3)))
      else
        let lhs, e = hoist_expr Unspecified e in
        nest lhs e.typ e

  | ESwitch (e1, branches) ->
      if e.typ = TUnit then
        let lhs, e1 = hoist_expr Unspecified e1 in
        let branches = List.map (fun (tag, e2) -> tag, hoist_stmt e2) branches in
        nest lhs e.typ (mk (ESwitch (e1, branches)))
      else
        let lhs, e = hoist_expr Unspecified e in
        nest lhs e.typ e

  | EFor (binder, e1, e2, e3, e4) ->
      assert (e.typ = TUnit);
      (* The semantics is that [e1] is evaluated once, so it's fine to hoist any
       * let-bindings it generates. *)
      let lhs1, e1 = hoist_expr (if binder.node.meta = Some MetaSequence then UnderStmtLet else Unspecified) e1 in
      let binder, s = opening_binder binder in
      let e2 = s e2 and e3 = s e3 and e4 = s e4 in
      (* [e2] and [e3], however, are evaluated at each loop iteration! *)
      let lhs2, e2 = hoist_expr Unspecified e2 in
      let lhs3, e3 = hoist_expr UnderStmtLet e3 in
      if lhs2 <> [] || lhs3 <> [] then
        fatal_error "The translation of this for-loop's condition or iteration \
          expression gives rise to intermediary let-bindings!\n\
          %a\n\
          Let-bindings are:\n\
          %a" ppexpr e pplbs (lhs2 @ lhs3);
      let e4 = hoist_stmt e4 in
      let s = closing_binder binder in
      nest lhs1 e.typ (mk (EFor (binder, e1, s e2, s e3, s e4)))

  | EWhile (e1, e2) ->
      (* All of the following cases are valid statements (their return type is
       * [TUnit]. *)
      assert (e.typ = TUnit);
      let lhs, e1 = hoist_expr Unspecified e1 in
      if lhs <> [] then
        fatal_error "The translation of this while loop's condition expression \
          gives rise to let-bindings!\n\
          %a\n\
          Let-bindings are:\n\
          %a" ppexpr e pplbs lhs;
      let e2 = hoist_stmt e2 in
      mk (EWhile (e1, e2))

  | EAssign (e1, e2) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let lhs2, e2 = hoist_expr AssignRhs e2 in
      nest (lhs1 @ lhs2) e.typ (mk (EAssign (e1, e2)))

  | EBufWrite (e1, e2, e3) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      let lhs3, e3 = hoist_expr Unspecified e3 in
      nest (lhs1 @ lhs2 @ lhs3) e.typ (mk (EBufWrite (e1, e2, e3)))

  | EBufBlit (e1, e2, e3, e4, e5) ->
      assert (e.typ = TUnit);
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      let lhs3, e3 = hoist_expr Unspecified e3 in
      let lhs4, e4 = hoist_expr Unspecified e4 in
      let lhs5, e5 = hoist_expr Unspecified e5 in
      nest (lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5) e.typ (mk (EBufBlit (e1, e2, e3, e4, e5)))

  | EReturn e ->
      let lhs, e = hoist_expr Unspecified e in
      nest lhs e.typ (mk (EReturn e))

  | EBreak ->
      mk EBreak

  | EComment (s, e, s') ->
      mk (EComment (s, hoist_stmt e, s'))

  | EMatch _ ->
      failwith "[hoist_t]: EMatch not properly desugared"

  | ETuple _ ->
      failwith "[hoist_t]: ETuple not properly desugared"

  | ESequence _ ->
      failwith "[hoist_t]: sequences should've been translated as let _ ="

  | _ ->
      let lhs, e = hoist_expr Unspecified e in
      nest lhs e.typ e

(* This function returns an expression that can be successfully translated as a
 * C* expression. *)
and hoist_expr pos e =
  let mk node = { node; typ = e.typ } in
  match e.node with
  | ETApp _ ->
      assert false

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
  | EAddrOf _
  | EOp _ ->
      [], e

  | EComment (s, e, s') ->
      let lhs, e = hoist_expr Unspecified e in
      lhs, mk (EComment (s, e, s'))

  | EIgnore e ->
      let lhs, e = hoist_expr Unspecified e in
      lhs, mk (EIgnore e)

  | EApp (e, es) ->
      (* TODO: assert that in the case of a lazily evaluated boolean operator,
       * there are no intermediary let-bindings there... or does F* guarantee
       * that no effectful computations can occur there? *)
      let lhs, e = hoist_expr Unspecified e in
      let lhss, es = List.split (List.map (hoist_expr Unspecified) es) in
      (* TODO: reverse the order and use [rev_append] here *)
      let lhs = lhs @ List.flatten lhss in
      lhs, mk (EApp (e, es))

  | ELet (binder, e1, e2) ->
      let lhs1, e1 = hoist_expr UnderStmtLet e1 in
      let binder, e2 = open_binder binder e2 in
      (* The caller (e.g. [hoist_t]) takes care, via [nest], of closing this
       * binder. *)
      let lhs2, e2 = hoist_expr pos e2 in
      lhs1 @ [ binder, e1 ] @ lhs2, e2

  | EIfThenElse (e1, e2, e3) ->
      let t = e.typ in
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let e2 = hoist_stmt e2 in
      let e3 = hoist_stmt e3 in
      if pos = UnderStmtLet then
        lhs1, mk (EIfThenElse (e1, e2, e3))
      else
        let b, body, cont = mk_named_binding "ite" t (EIfThenElse (e1, e2, e3)) in
        lhs1 @ [ b, body ], cont

  | ESwitch (e1, branches) ->
      let t = e.typ in
      let lhs, e1 = hoist_expr Unspecified e1 in
      let branches = List.map (fun (tag, e) -> tag, hoist_stmt e) branches in
      if pos = UnderStmtLet then
        lhs, mk (ESwitch (e1, branches))
      else
        let b, body, cont = mk_named_binding "sw" t (ESwitch (e1, branches)) in
        lhs @ [ b, body ], cont

  | EWhile (e1, e2) ->
      let lhs1, e1 = hoist_expr Unspecified e1 in
      if lhs1 <> [] then
        fatal_error "The translation of this while loop's condition expression \
          gives rise to let-bindings!\n\
          %a\n\
          Let-bindings are:\n\
          %a" ppexpr e pplbs lhs1;
      let e2 = hoist_stmt e2 in
      if pos = UnderStmtLet then
        [], mk (EWhile (e1, e2))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        [ b, mk (EWhile (e1, e2)) ], mk EUnit

  | EFor (binder, e1, e2, e3, e4) ->
      let lhs1, e1 = hoist_expr (if binder.node.meta = Some MetaSequence then UnderStmtLet else Unspecified) e1 in
      let binder, s = opening_binder binder in
      let e2 = s e2 and e3 = s e3 and e4 = s e4 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      let lhs3, e3 = hoist_expr UnderStmtLet e3 in
      if lhs2 <> [] || lhs3 <> [] then
        fatal_error "The translation of this for-loop's condition or iteration \
          expression gives rise to intermediary let-bindings!\n\
          %a\n\
          Let-bindings are:\n\
          %a" ppexpr e pplbs (lhs2 @ lhs3);
      let e4 = hoist_stmt e4 in
      let s = closing_binder binder in
      if pos = UnderStmtLet then
        lhs1, mk (EFor (binder, e1, s e2, s e3, s e4))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs1 @ [ b, mk (EFor (binder, e1, s e2, s e3, s e4)) ], mk EUnit

  | EFun (binders, expr, t) ->
      let binders, expr = open_binders binders expr in
      let expr = hoist_stmt expr in
      let expr = close_binders binders expr in
      [], mk (EFun (binders, expr, t))

  | EAssign (e1, e2) ->
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let rhspos = if is_array e1.typ then AssignRhs else Unspecified in
      let lhs2, e2 = hoist_expr rhspos e2 in
      if pos = UnderStmtLet then
        lhs1 @ lhs2, mk (EAssign (e1, e2))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs1 @ lhs2 @ [ b, mk (EAssign (e1, e2)) ], mk EUnit

  | EBufCreate (l, e1, e2) ->
      let t = e.typ in
      let lhs1, e1 = hoist_expr BufAssignee e1 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      if pos = UnderStmtLet || pos = AssignRhs then
        lhs1 @ lhs2, mk (EBufCreate (l, e1, e2))
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreate (l, e1, e2)) in
        lhs1 @ lhs2 @ [ b, body ], cont

  | EBufCreateL (l, es) ->
      let t = e.typ in
      let lhs, es = List.split (List.map (hoist_expr BufAssignee) es) in
      let lhs = List.flatten lhs in
      if pos = UnderStmtLet || pos = AssignRhs then
        lhs, mk (EBufCreateL (l, es))
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreateL (l, es)) in
        lhs @ [ b, body ], cont

  | EBufRead (e1, e2) ->
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      lhs1 @ lhs2, mk (EBufRead (e1, e2))

  | EBufWrite (e1, e2, e3) ->
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      let lhs3, e3 = hoist_expr BufAssignee e3 in
      let lhs = lhs1 @ lhs2 @ lhs3 in
      if pos = UnderStmtLet then
        lhs, mk (EBufWrite (e1, e2, e3))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufWrite (e1, e2, e3)) ], mk EUnit

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      let lhs3, e3 = hoist_expr Unspecified e3 in
      let lhs4, e4 = hoist_expr Unspecified e4 in
      let lhs5, e5 = hoist_expr Unspecified e5 in
      let lhs = lhs1 @ lhs2 @ lhs3 @ lhs4 @ lhs5 in
      if pos = UnderStmtLet then
        lhs, mk (EBufBlit (e1, e2, e3, e4, e5))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufBlit (e1, e2, e3, e4, e5)) ], mk EUnit

  | EBufFill (e1, e2, e3) ->
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      let lhs3, e3 = hoist_expr Unspecified e3 in
      let lhs = lhs1 @ lhs2 @ lhs3 in
      if pos = UnderStmtLet then
        lhs, mk (EBufFill (e1, e2, e3))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufFill (e1, e2, e3)) ], mk EUnit

  | EBufFree e ->
      let lhs, e = hoist_expr Unspecified e in
      if pos = UnderStmtLet then
        lhs, mk (EBufFree e)
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs @ [ b, mk (EBufFree e) ], mk EUnit

  | EBufSub (e1, e2) ->
      let lhs1, e1 = hoist_expr Unspecified e1 in
      let lhs2, e2 = hoist_expr Unspecified e2 in
      lhs1 @ lhs2, mk (EBufSub (e1, e2))

  | ECast (e, t) ->
      let lhs, e = hoist_expr Unspecified e in
      lhs, mk (ECast (e, t))

  | EField (e, f) ->
      let lhs, e = hoist_expr Unspecified e in
      lhs, mk (EField (e, f))

  | EFlat fields ->
      let lhs, fields = List.split (List.map (fun (ident, expr) ->
        let lhs, expr = hoist_expr Unspecified expr in
        lhs, (ident, expr)
      ) fields) in
      begin match pos with
      | UnderStmtLet ->
          List.flatten lhs, mk (EFlat fields)
      | BufAssignee | AssignRhs when !Options.compound_literals = `Wasm ->
          List.flatten lhs, mk (EFlat fields)
      | _ when !Options.compound_literals = `Ok ->
          List.flatten lhs, mk (EFlat fields)
      | _ ->
          let b, body, cont = mk_named_binding "flat" e.typ (EFlat fields) in
          List.flatten lhs @ [ b, body ], cont
      end

  | ECons _ ->
      failwith "[hoist_t]: ECons, why?"

  | ETuple _ ->
      failwith "[hoist_t]: ETuple not properly desugared"

  | EMatch _ ->
      failwith "[hoist_t]: EMatch"

  | ESequence _ ->
      fatal_error "[hoist_t]: sequences should've been translated as let _ ="

  | EReturn _ | EBreak ->
      raise_error (Unsupported "[return] or [break] expressions should only appear in statement position")

(* TODO: figure out if we want to ignore the other cases for performance
 * reasons. *)
let hoist = object
  inherit [_] map

  method! visit_DFunction _ cc flags n ret name binders expr =
    (* TODO: no nested let-bindings in top-level value declarations either *)
    let binders, expr = open_binders binders expr in
    let expr = hoist_stmt expr in
    let expr = close_binders binders expr in
    DFunction (cc, flags, n, ret, name, binders, expr)
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
  with_type e.typ (match e.node with
  | ELet (_, ({ node = (EIfThenElse _ | ESwitch _); _ } as e), { node = EBound 0; _ }) ->
      (fixup_return_pos e).node
  | ELet (_, ({ node = (EIfThenElse _ | ESwitch _); _ } as e),
    { node = ECast ({ node = EBound 0; _ }, t); _ }) ->
      (nest_in_return_pos t (fun _ e -> with_type t (ECast (e, t))) (fixup_return_pos e)).node
  | EIfThenElse (e1, e2, e3) ->
      EIfThenElse (e1, fixup_return_pos e2, fixup_return_pos e3)
  | ESwitch (e1, branches) ->
      ESwitch (e1, List.map (fun (t, e) -> t, fixup_return_pos e) branches)
  | ELet (b, e1, e2) ->
      ELet (b, e1, fixup_return_pos e2)
  | e ->
      e
  )

(* TODO: figure out if we want to ignore the other cases for performance
 * reasons. *)
let fixup_hoist = object
  inherit [_] map

  method visit_DFunction _ cc flags n ret name binders expr =
    DFunction (cc, flags, n, ret, name, binders, fixup_return_pos expr)
end




(* Make top-level names C-compatible using a global translation table **********)

let skip_prefix prefix =
  List.exists ((=) (String.concat "." prefix)) !Options.no_prefix

let target_c_name lident =
  if skip_prefix (fst lident) then
    snd lident
  else
    string_of_lident lident

let record_name lident =
  [], GlobalNames.record (string_of_lident lident) (target_c_name lident)


let record_toplevel_names = object (self)
  inherit [_] map

  method! visit_DGlobal _ flags name n t body =
    DGlobal (flags, record_name name, n, t, body)

  method! visit_DFunction _ cc flags n ret name args body =
    DFunction (cc, flags, n, ret, record_name name, args, body)

  method! visit_DExternal _ cc flags name t =
    DExternal (cc, flags, record_name name, t)

  method! visit_DType env name flags n t =
    (* TODO: this is not correct since record_name might, on the second call
     * (not forward), return something disambiguated with a suffix. *)
    let name = if t = Forward then name else record_name name in
    DType (name, flags, n, self#visit_type_def env t)

  method! visit_Enum _ tags =
    Enum (List.map record_name tags)
end


let t lident =
  [], GlobalNames.translate (string_of_lident lident) (target_c_name lident)

let replace_references_to_toplevel_names = object
  inherit [_] map

  method! visit_lident _ lident =
    t lident
end

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
 *   let b = if true then b1 <-copy-- bufcreatel ...; subbuf b1 0 else ...
 *
 * This introduces a new copy-assignment operator (encoded via an assignment
 * whose type is Array instead of Buf) which is implemented as a memcpy later
 * on.
 *
 * This function assumes [hoist] has been run so that every single [EBufCreate]
 * appears as a [let x = bufcreate...], always in statement position.
 * The [hoist] transformation will be called a second time (after inlining)
 * meaning that it will encounter nodes of the form [b1 <-copy-- bufcreatel];
 * [hoist] may be tempted to hoist these buffer create operations, but thanks to
 * the [AssignRhs] case, knows that it shouldn't. *)
let rec hoist_bufcreate (e: expr) =
  let mk node = { node; typ = e.typ } in
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
       * This bit is really important because it makes sure that the assignment
       * becomes a Copy node (see AstToCStar), which has different semantics
       * than an assignment. This is (as far as I know) the only place that
       * generates these copy nodes. *)
      begin match strengthen_array b.typ e1 with
      | TArray (t, size) as tarray ->
          let b, e2 = open_binder b e2 in
          (* Any assignments into this one will be desugared as a
           * copy-assignment, thanks to the strengthened type. *)
          let b = { b with typ = tarray } in
          let bs, e2 = hoist_bufcreate e2 in
          (* WASM/C discrepancy; in C, the array type makes sure we allocate
           * stack space. In Wasm, we rely on the expression to actually
           * generate run-time code. *)
          let init = with_type (TBuf t) (
            EBufCreate (Common.Stack, any, with_type uint32 (EConstant size)))
          in
          (mark_mut b, init) :: bs,
          begin match e1.node with
          | EAny ->
              failwith "not allowing that per WASM restrictions"
          | EBufCreate (_, { node = EAny; _ }, _) ->
              (* We're visiting this node again. *)
              e2
          | _ ->
              (* Need actual copy-assigment. *)
              mk (ELet (sequence_binding (),
                with_unit (EAssign (with_type tarray (EOpen (b.node.name, b.node.atom)), e1)),
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

and under_pushframe (e: expr) =
  let mk node = { node; typ = e.typ } in
  match e.node with
  | ELet (b, e1, e2) ->
      let b1, e1 = hoist_bufcreate e1 in
      let e2 = under_pushframe e2 in
      nest b1 e.typ (mk (ELet (b, e1, e2)))
  | _ ->
      let b, e' = hoist_bufcreate e in
      nest b e.typ e'

(* This function skips the first few statements until we hit the first
 * push_frame, and then starts hoisting. The reason for that is:
 * - either whatever happens before push is benign
 * - or, something happens (e.g. allocation), and this means that the function
 *   WILL be inlined, and that its caller will take care of hoisting things up
 *   in the second round.
 * Note: we could do this in a simpler manner with a visitor whose env is a
 * [ref * (list (binder * expr))] but that would degrade the quality of the
 * code. This recursive routine is smarter and preserves the sequence of
 * let-bindings starting from the beginning of the scope. *)
let rec skip (e: expr) =
  let mk node = { node; typ = e.typ } in
  match e.node with
  | ELet (b, ({ node = EPushFrame; _ } as e1), e2) ->
      mk (ELet (b, e1, under_pushframe e2))
  | ELet (b, e1, e2) ->
      mk (ELet (b, e1, skip e2))
  (* Descend into conditionals that are in return position. *)
  | EIfThenElse (e1, e2, e3) ->
      mk (EIfThenElse (e1, skip e2, skip e3))
  | ESwitch (e, branches) ->
      mk (ESwitch (e, List.map (fun (t, e) -> t, skip e) branches))
  | _ ->
      e

(* TODO: figure out if we want to ignore the other cases for performance
 * reasons. *)
let hoist_bufcreate = object
  inherit [_] map

  method visit_DFunction () cc flags n ret name binders expr =
    try
      DFunction (cc, flags, n, ret, name, binders, skip expr)
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
    (* Relying on the invariant that, if [finish] is effectful, F* has
     * hoisted it *)
    if not (is_value finish) then
      Warnings.fatal_error "%a is not a value" pexpr finish;
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
    | EQualified ([ "C"; "Loops" ], "for_"), [ start; finish; _inv; { node = EFun (_, body, _); _ } ] ->
        self#mk_for start finish body K.UInt32

    | EQualified ([ "C"; "Loops" ], "for64"), [ start; finish; _inv; { node = EFun (_, body, _); _ } ] ->
        self#mk_for start finish body K.UInt64

    | EQualified ([ "C"; "Loops" ], s), [ _measure; _inv; tcontinue; body; init ]
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
                mk_app t (lift 2 body) (with_type t (EBound 0))
              ));
              with_unit (EAssign (
                with_type TBool (EBound 1),
                mk_app t (lift 2 tcontinue) (with_type t (EBound 0))
              ));
           ])
          ));
          with_type t (EBound 0);
        ]))))

    | EQualified ([ "C"; "Loops" ], "interruptible_for"), [ start; finish; _inv; { node = EFun (_, _, _); _ } as f ] ->
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

    | EQualified ([ "C"; "Loops" ], s), [
        { node = EFun (_, test, _); _ };
        { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "while" ->
        EWhile (DeBruijn.subst Helpers.eunit 0 test,
          DeBruijn.subst Helpers.eunit 0 body)

    | EQualified ([ "C"; "Loops" ], s), [ { node = EFun (_, body, _); _ } ]
      when KString.starts_with s "do_while" ->
        EWhile (etrue, with_unit (
          EIfThenElse (DeBruijn.subst eunit 0 (self#visit_expr_w () body),
            with_unit EBreak,
            eunit)))

    | _ ->
        super#visit_EApp ((), t) e es

end



(* The various series of rewritings called by Kremlin.ml **********************)

(* Debug any intermediary AST as follows: *)
(* PPrint.(Print.(print (PrintAst.print_files files ^^ hardline))); *)

(* Macros that may generate tuples and sequences. Run before data types
 * compilation, once. *)
let simplify0 (files: file list): file list =
  let files = remove_local_function_bindings#visit_files () files in
  let files = count_and_remove_locals#visit_files [] files in
  let files = remove_uu#visit_files () files in
  let files = combinators#visit_files () files in
  let files = wrapping_arithmetic#visit_files () files in
  files

(* Many phases rely on a statement like language where let-bindings, buffer
 * allocations and writes are hoisted; where if-then-else is always in statement
 * position; where sequences are not nested. These series of transformations
 * re-establish this invariant. *)
let simplify2 (files: file list): file list =
  let files = sequence_to_let#visit_files () files in
  (* Quality of hoisting is WIDELY improved if we remove un-necessary
   * let-bindings. *)
  let files = count_and_remove_locals#visit_files [] files in
  let files = hoist#visit_files () files in
  let files = if !Options.c89_scope then SimplifyC89.hoist_lets#visit_files (ref []) files else files in
  let files = hoist_bufcreate#visit_files () files in
  let files = fixup_hoist#visit_files () files in
  let files = let_if_to_assign#visit_files () files in
  let files = misc_cosmetic#visit_files () files in
  let files = let_to_sequence#visit_files () files in
  files

(* This should be run late since inlining may create more opportunities for the
 * removal of unused variables. *)
let remove_unused (files: file list): file list =
  let files = count_and_remove_locals#visit_files [] files in
  let map = Hashtbl.create 41 in
  (build_unused_map map)#visit_files () files;
  let files = (remove_unused_parameters map)#visit_files () files in
  files

(* Allocate C names avoiding keywords and name collisions. This should be done
 * as the last operations, otherwise, any table for memoization suddenly becomes
 * invalid. *)
let to_c_names (files: file list): file list =
  let files = record_toplevel_names#visit_files () files in
  let files = replace_references_to_toplevel_names#visit_files () files in
  files

