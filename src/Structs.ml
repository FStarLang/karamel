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
              let ret, args = flatten_arrow typ in
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
  let ret, args = flatten_arrow t in
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
  fold_arrow args ret

let will_be_lvalue e =
  match e.node with
  | EBound _ | EOpen _ | EBufRead _ ->
      true
  | _ ->
      false

(* Rewrite functions and expressions to take and possibly return struct
 * pointers. *)
let rewrite action_table = object (self)

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
        let ret_binder, ret_atom = Simplify.mk_binding "ret" (TBuf ret) in
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
        with_type TUnit (EBufWrite (Option.must ret_atom, Simplify.zerou32, body))
      else
        body
    in
    let body = DeBruijn.close_binders binders body in
    DFunction (cc, flags, n, ret, lid, binders, body)

  method dexternal _ cc lid t =
    match t with
    | TArrow _ ->
        (* Also rewrite external function declarations. *)
        let ret, args = flatten_arrow t in
        let ret_is_struct, args_are_structs = Hashtbl.find action_table lid in
        let buf_if arg is_struct = if is_struct then TBuf arg else arg in
        let ret, args =
          if ret_is_struct then
            TUnit, List.map2 buf_if args args_are_structs @ [ TBuf ret ]
          else
            ret, List.map2 buf_if args args_are_structs
        in
        DExternal (cc, lid, fold_arrow args ret)
    | _ ->
        DExternal (cc, lid, t)


  method! eopen to_be_starred t name atom =
    (* [x] was a strut parameter that is now passed by reference; replace it
     * with [*x] *)
    if List.exists (Atom.equal atom) to_be_starred then
      EBufRead (with_type (TBuf t) (EOpen (name, atom)), Simplify.zerou32)
    else
      EOpen (name, atom)

  method! eapp to_be_starred t e args =
    let module T = struct exception NotLowStar end in
    try match e.node with
    | EQualified lid ->
        let args = List.map (self#visit to_be_starred) args in
        (* Determine using our computed table which of the arguments and the
         * return type must be passed by reference. We could alternatively use
         * the type of [e], but it sometimes may be incomplete. *)
        let ret_is_struct, args_are_structs = Hashtbl.find action_table lid in

        (* Partial application. Not Low*... bail. *)
        if List.length args_are_structs <> List.length args then
          raise T.NotLowStar;

        (* Ensure things remain well-typed. *)
        let e = with_type (rewrite_function_type (ret_is_struct, args_are_structs) e.typ) (EQualified lid) in

        (* At call-site, [f e] can only be transformed into [f &e] is [e] is an
         * [lvalue]. This is, sadly, a little bit of an anticipation over the
         * ast-to-C* translation phase. TODO remove the check, and rely on
         * AstToCStar or a Simplify phase to fix this. *)
        let bs, args = KList.fold_lefti (fun i (bs, es) (e, is_struct) ->
          if is_struct then
            if will_be_lvalue e then
              bs, with_type (TBuf e.typ) (EAddrOf e) :: es
            else
              let x, atom = Simplify.mk_binding (Printf.sprintf "s%d" i) e.typ in
              (x, e) :: bs, with_type (TBuf e.typ) (EAddrOf atom) :: es
          else
            bs, e :: es
        ) ([], []) (List.combine args args_are_structs) in
        let args = List.rev args in

        if ret_is_struct then
          (* [let ret in f args &ret; *ret] *)
          let x, atom = Simplify.mk_binding "ret" t in
          let bs = (x, with_type TAny EAny) :: bs in
          let args = args @ [ with_type (TBuf t) (EAddrOf atom) ] in
          (Simplify.nest bs t (with_type t (ESequence [
            with_type TUnit (EApp (e, args));
            atom]))).node
        else
          (Simplify.nest bs t (with_type t (EApp (e, args)))).node
    | _ ->
        EApp (e, List.map (self#visit to_be_starred) args)
    with Not_found | T.NotLowStar ->
      EApp (e, List.map (self#visit to_be_starred) args)

end

let rewrite files =
  let action_table = mk_action_table files in
  Simplify.visit_files [] (rewrite action_table) files
