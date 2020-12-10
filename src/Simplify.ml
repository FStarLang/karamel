(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 License. *)

(** This module rewrites the original AST to send it into Low*, the subset we
 * know how to translate to C. *)

open Ast
open DeBruijn
open Warn
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

  method private remove_trivial_let e =
    match e with
    | ELet (_, e1, { node = EBound 0; _ }) when Helpers.is_readonly_c_expression e1 ->
        e1.node
    | _ ->
        e

  method! visit_ELet (env, _) b e1 e2 =
    (* Remove unused variables. Important to get rid of calls to [HST.get()]. *)
    let e1 = self#visit_expr_w env e1 in
    let env = self#extend env b in
    let e2 = self#visit_expr_w env e2 in
    if !(b.node.mark) = 0 && is_readonly_c_expression e1 then
      self#remove_trivial_let (snd (open_binder b e2)).node
    else if !(b.node.mark) = 0 then
      if e1.typ = TUnit then
        self#remove_trivial_let (ELet ({ b with node = { b.node with meta = Some MetaSequence }}, e1, e2))
      else
        (* We know the variable is unused... but its body cannot be determined
         * to be readonly, so we have to keep it. What's better?
         *   int unused = f();
         * or:
         *   (void)f(); ? *)
        (* ELet ({ node = { b.node with meta = Some MetaSequence }; typ = TUnit}, push_ignore e1, e2) *)
        self#remove_trivial_let (ELet (b, e1, e2))
    else
      self#remove_trivial_let (ELet (b, e1, e2))

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

(* Unused parameter elimination ***********************************************)

(* Done by typing (in general), and based on usage information (strictly for
 * static, first-order functions. Relies on an accurate count from
 * count_and_remove_locals. *)

(* Build a table that maps each lid to a list of booleans, where true indicates
 * that the parameter is unused in the body. *)

let unused_parameter_table = object (_)

  inherit [_] iter

  method! visit_DFunction parameter_table _ flags _ _ name binders _ =
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
      List.nth l i = 0
    ) ||
    (* Second case: it's a unit, so here type-based elimination *)
    List.nth ts i = TUnit
  in
  unused_i i &&
  implies (i = 0) (List.exists not (KList.make (List.length ts) unused_i))

let remove_unused_parameters = object (self)
  inherit [_] map

  val mutable current_lid = [], ""

  method! extend (table, j) _ =
    table, j + 1

  method! visit_DFunction (parameter_table, _) cc flags n ret name binders body =
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
    ) body (KList.make n_binders (fun i -> i)) in
    let binders = KList.filter_mapi (fun i b -> if unused i then None else Some b) binders in
    DFunction (cc, flags, n, ret, name, binders, body)

  method! visit_TArrow (parameter_table, _) t1 t2 =
    (* Important: the only entries in `parameter_table` are those which are
     * first order, i.e. for which the only occurrence is under an EApp, which
     * does *not* recurse into visit_TArrow! *)
    let dummy_lid = [], "" in
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
              (List.mapi (fun k count ->
                (* 0 is the last parameter, l - 1 the first *)
                if k == l - 1 - (j - i) then begin
                  assert (count > 0);
                  count - 1
                end else
                  count
              ) (Hashtbl.find private_use_table current_lid))
        | _ -> ()
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
      let used = KList.make (List.length ts) (fun i -> not (unused i)) in
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
    if Helpers.is_uu b.node.name &&
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

(* Transform functional updates of the form x.(i) <- { x.(i) with f = e } into
 * in-place field updates. *)
let functional_updates = object (self)

  inherit [_] map

  val mutable make_mut = []

  method! visit_ELet env b e1 e2 =
    let b = self#visit_binder env b in
    let e1 = self#visit_expr env e1 in

    let make_assignment fields k =
      let the_field, _ = List.partition (function
          | Some f, { node = EField ({ node = EBound 0; _ }, f'); _ } when f = f' ->
              false
          | _ ->
              true
        ) fields in
      if List.length the_field = 1 then
        let the_field, the_expr = List.hd the_field in
        let the_field = Option.must the_field in
        let the_expr = self#visit_expr env (snd (open_binder b the_expr)) in
        make_mut <- (assert_tlid e1.typ, the_field) :: make_mut;
        k (EAssign (with_type the_expr.typ (EField (e1, the_field)), the_expr))
      else
        ELet (b, e1, self#visit_expr env e2)
    in

    match e1.node, e2.node with
    | EBufRead ({ node = EBound i; _ }, j),
      EBufWrite ({ node = EBound iplusone; _ }, j', { node = EFlat fields; _ })
      when j = j' && iplusone = i + 1 ->
        (* let uu = (Bound i)[j];
         * (Bound (i + 1))[j] <- { fi = ei } with ei = e if i = k, (Bound 0).fi otherwise
         * -->
         * (Bound i)[j].fk <- (unlift 1 e)
         *)
        make_assignment fields (fun x -> x)

    | EBufRead ({ node = EBound i; _ }, j),
      ELet (b,
        { node = EBufWrite ({ node = EBound iplusone; _ }, j', { node = EFlat fields; _ }); _ },
        e3)
      when j = j' && iplusone = i + 1 ->
        (* let uu = (Bound i)[j];
         * let _ = (Bound (i + 1))[j] <- { fi = ei } with ei = e if i = k, * (Bound 0).fi otherwise in
         * e3
         * -->
         * let _ = (Bound i)[j].fk <- (unlift 1 e) in
         * e3
         *)
        make_assignment fields (fun x ->
          let e3 = self#visit_expr env (snd (open_binder b e3)) in
          ELet (b, with_unit x, e3))

    | _ ->
        ELet (b, e1, self#visit_expr env e2)

  (* The same object is called a second time with the mark_mut flag set to true
   * to mark those fields that now ought to be mutable *)
  method! visit_DType mark_mut name flags n def =
    match def with
    | Flat fields when mark_mut ->
        let fields = List.map (fun (f, (t, m)) ->
          if List.exists (fun (name', f') -> Some f' = f && name' = name) make_mut then
            f, (t, true)
          else
            f, (t, m)
        ) fields in
        DType (name, flags, n, Flat fields)
    | _ ->
        DType (name, flags, n, def)
end

let misc_cosmetic = object (self)

  inherit [_] map as super

  val mutable count = 0

  method! visit_ELet env b e1 e2 =
    let b = self#visit_binder env b in
    let e1 = self#visit_expr env e1 in
    match e1.node with
    | EBufCreate (Common.Stack, e1, { node = EConstant (_, "1"); _ }) when not !Options.wasm ->
        (* int x[1]; x[0] = e; x
         * -->
         * int x; x = e; &x *)
        let t = assert_tbuf_or_tarray b.typ in
        let b = with_type t { b.node with mut = true } in
        let ref = with_type (TBuf (t, false)) (EAddrOf (with_type t (EBound 0))) in
        ELet (b, e1, self#visit_expr env (DeBruijn.subst_no_open ref 0 e2))

    | _ ->
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
      if List.length lhs2 > 0 && not !Options.wasm then begin
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
      if e.typ = TUnit then
        let lhs, e1 = hoist_expr loc Unspecified e1 in
        let e2 = hoist_stmt loc e2 in
        let e3 = hoist_stmt loc e3 in
        nest lhs e.typ (mk (EIfThenElse (e1, e2, e3)))
      else
        let lhs, e = hoist_expr loc Unspecified e in
        nest lhs e.typ e

  | ESwitch (e1, branches) ->
      if e.typ = TUnit then
        let lhs, e1 = hoist_expr loc Unspecified e1 in
        let branches = List.map (fun (tag, e2) -> tag, hoist_stmt loc e2) branches in
        nest lhs e.typ (mk (ESwitch (e1, branches)))
      else
        let lhs, e = hoist_expr loc Unspecified e in
        nest lhs e.typ e

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
      if lhs2 <> [] || lhs3 <> [] then
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc loc,
          GeneratesLetBindings ("this for-loop's condition or iteration", e, (lhs2 @ lhs3))));
      let e4 = hoist_stmt loc e4 in
      let s = closing_binder binder in
      nest lhs1 e.typ (mk (EFor (binder, e1, s e2, s e3, s e4)))

  | EWhile (e1, e2) ->
      (* All of the following cases are valid statements (their return type is
       * [TUnit]. *)
      assert (e.typ = TUnit);
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

  | EComment (s, e, s') ->
      mk (EComment (s, hoist_stmt loc e, s'))

  | EMatch _ ->
      failwith "[hoist_t]: EMatch not properly desugared"

  | ETuple _ ->
      failwith "[hoist_t]: ETuple not properly desugared"

  | ESequence _ ->
      failwith "[hoist_t]: sequences should've been translated as let _ ="

  | _ ->
      let lhs, e = hoist_expr loc Unspecified e in
      nest lhs e.typ e

(* This function returns an expression that can be successfully translated as a
 * C* expression. *)
and hoist_expr loc pos e =
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
  | EStandaloneComment _
  | EOp _ ->
      [], e

  | EComment (s, e, s') ->
      let lhs, e = hoist_expr loc Unspecified e in
      lhs, mk (EComment (s, e, s'))

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
      if lhs2 <> [] || lhs3 <> [] then
        Warn.(maybe_fatal_error (KPrint.bsprintf "%a" Loc.ploc loc,
          GeneratesLetBindings ("this for-loop's condition or iteration", e, (lhs2 @ lhs3))));
      let e4 = hoist_stmt loc e4 in
      let s = closing_binder binder in
      if pos = UnderStmtLet then
        lhs1, mk (EFor (binder, e1, s e2, s e3, s e4))
      else
        let b = fresh_binder "_" TUnit in
        let b = { b with node = { b.node with meta = Some MetaSequence }} in
        lhs1 @ [ b, mk (EFor (binder, e1, s e2, s e3, s e4)) ], mk EUnit

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
      let lhs2, e2 = hoist_expr loc Unspecified e2 in
      if pos = UnderStmtLet then
        lhs1 @ lhs2, mk (EBufCreate (l, e1, e2))
      else
        let b, body, cont = mk_named_binding "buf" t (EBufCreate (l, e1, e2)) in
        lhs1 @ lhs2 @ [ b, body ], cont

  | EBufCreateL (l, es) ->
      let t = e.typ in
      let lhs, es = List.split (List.map (hoist_expr loc Unspecified) es) in
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
  inherit [_] map as super

  method! visit_file loc file =
    super#visit_file Loc.(File (fst file) :: loc) file

  method! visit_DFunction loc cc flags n ret name binders expr =
    let loc = Loc.(InTop name :: loc) in
    (* TODO: no nested let-bindings in top-level value declarations either *)
    let binders, expr = open_binders binders expr in
    let expr = hoist_stmt loc expr in
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

(* A reverse map whose domain is all the top-level declarations that end up
 * in a .h file. Notably, private functions are absent from the map. *)
let original_of_c_name: (ident, lident) Hashtbl.t = Hashtbl.create 43

type scope_env = GlobalNames.t * (string, GlobalNames.t) Hashtbl.t

class scope_helpers = object (self)
  val mutable current_file = ""

  method private is_private_scope flags lident =
    List.mem Common.Private flags && not (Helpers.is_static_header lident)

  method private record (global_scope, local_scopes) is_external flags lident =
    let is_macro = List.mem Common.Macro flags in
    let is_private = self#is_private_scope flags lident in
    let local_scope = Hashtbl.find local_scopes current_file in
    let attempt_shortening = is_private && not is_external in
    let target = GlobalNames.target_c_name ~attempt_shortening ~is_macro lident in
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
    self#record env false flags name

  method! visit_DFunction env _ flags _ _ name _ _ =
    self#record env false flags name

  method! visit_DExternal env _ flags name _ _ =
    self#record env true flags name

  val forward = Hashtbl.create 41

  method! visit_DType env name flags _ def =
    if not (Hashtbl.mem forward name) then
      self#record env false flags name;
    match def with
    | Enum lids -> List.iter (self#record env false flags) lids
    | Forward -> Hashtbl.add forward name ()
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
            let stmts = KList.filter_some (List.map2 (fun x arg ->
              (* Don't generate x = x as this is oftentimes a fatal warning. *)
              if x = arg then
                None
              else
                Some (with_unit (EAssign (x, arg)))
            ) a_args args) in
            if stmts = [] then
              EUnit
            else
              ESequence stmts

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

    method! visit_DFunction () cc flags n ret name binders body =
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
            with_type ret (EAbort (Some "unreachable, returns inserted above"))
          ]))
        in
        DFunction (cc, flags, n, ret, name, binders, body)
      with
      | T.NotTailCall ->
          Warn.(maybe_fatal_error ("", NotTailCall name));
          DFunction (cc, flags, n, ret, name, binders, body)
      | T.NothingToTailCall ->
          DFunction (cc, flags, n, ret, name, binders, body)
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
       * Instead of using an encoding of copy-assignments, we actually generate
       * proper instructions now. *)
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
          let init = with_type (TBuf (t, false)) (
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
      mk (ELet (b, skip e1, skip e2))
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

(* This removes superfluous units. Useful for top-level constants that may have
 * calls of the form recall foobar in them. *)
let simplify1 (files: file list): file list =
  let files = sequence_to_let#visit_files () files in
  let files = count_and_remove_locals#visit_files [] files in
  let files = let_to_sequence#visit_files () files in
  files

(* Many phases rely on a statement-like language where let-bindings, buffer
 * allocations and writes are hoisted; where if-then-else is always in statement
 * position; where sequences are not nested. These series of transformations
 * re-establish this invariant. *)
let simplify2 (files: file list): file list =
  let files = sequence_to_let#visit_files () files in
  (* Quality of hoisting is WIDELY improved if we remove un-necessary
   * let-bindings. *)
  let files = count_and_remove_locals#visit_files [] files in
  let files = fixup_while_tests#visit_files () files in
  let files = hoist#visit_files [] files in
  let files = if !Options.c89_scope then SimplifyC89.hoist_lets#visit_files (ref []) files else files in
  let files = hoist_bufcreate#visit_files () files in
  let files = fixup_hoist#visit_files () files in
  let files = let_if_to_assign#visit_files () files in
  let files = misc_cosmetic#visit_files () files in
  let files = functional_updates#visit_files false files in
  let files = functional_updates#visit_files true files in
  let files = let_to_sequence#visit_files () files in
  files

(* This should be run late since inlining may create more opportunities for the
 * removal of unused variables. *)
let remove_unused (files: file list): file list =
  let parameter_table = Hashtbl.create 41 in
  let files = count_and_remove_locals#visit_files [] files in
  unused_parameter_table#visit_files parameter_table files;
  ignore_non_first_order#visit_files parameter_table files;
  let files = remove_unused_parameters#visit_files (parameter_table, 0) files in
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

(* Allocate C names avoiding keywords and name collisions. *)
let allocate_c_names (files: file list): (lident, ident) Hashtbl.t =
  let env = GlobalNames.create (), Hashtbl.create 41 in
  record_toplevel_names#visit_files env files;
  GlobalNames.mapping (fst env)
