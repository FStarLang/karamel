open Ast
open Helpers
(* open PrintAst.Ops *)

module C = Common
module K = Constant

let is_mutual map current_ty is_mut_lid =
  match current_ty with
  | None -> false
  | Some(current_ty) ->
    try Hashtbl.find (Hashtbl.find map current_ty) is_mut_lid; true with
    | Not_found -> false

let is_mutual_type map = function
| TBuf (TApp (lid, _))
| TBuf (TQualified lid) when Hashtbl.mem map lid -> true
| _ -> false

let mutual_behind_ptr _mutual_map = object (_self)
  val mutable current_ty = None

  inherit [unit] map

  (* method! dtype env name flags n d fwd_decl =
    let env = self#extend_tmany env n in
    current_ty <- Some name;
    let def = self#type_def env (Some name) d in
    current_ty <- None;
    DType (name, flags, n, def, fwd_decl) *)

  (* method! ematch env typ e branches =
    let old_ty = current_ty in
    (match typ with
    | TBuf (TApp (lid, _))
    | TBuf (TQualified lid) ->
      current_ty <- Some lid
    | _  -> ());
    KPrint.beprintf "%a scrut type" ptyp typ;
    let scrut = self#visit env e in
    let bs = self#branches env branches in
    current_ty <- old_ty;
    EMatch(scrut, bs) *)

  (* method! tqualified _env lid =
    (* Every occurrence of a mutual recursive type `t` becomes `TBuf t` *)
    if is_mutual mutual_map current_ty lid then
      TBuf (TQualified lid)
    else
      TQualified lid

  method! tapp env lid ts =
    let ts = List.map (self#visit_t env) ts in
    if is_mutual mutual_map current_ty lid then
      TBuf (TApp (lid, ts))
    else
      TApp (lid, ts) *)

   (* method! pcons env t cons args =
     (* A cons pattern needs to dereference the scrutinee first. *)
     let args = List.map (self#visit_pattern env) args in
     KPrint.beprintf "%a pat type\n" ptyp t;
     if is_mutual_type mutual_map t then
       PDeref (with_type (assert_tbuf t) (PCons (cons, args)))
     else
       PCons (cons, args)

   method! precord env t fields =
     (* Same for record patterns *)
     let fields = List.map (fun (f, t) -> f, self#visit_pattern env t) fields in
     if is_mutual_type mutual_map t then
       PDeref (with_type (assert_tbuf t) (PRecord fields))
     else
       PRecord fields

   method! econs env t cons args =
     (* Constructors now heap-allocate. *)
     let args = List.map (self#visit env) args in
     if is_mutual_type mutual_map t then
       EBufCreate (C.Eternal, with_type (assert_tbuf t) (ECons (cons, args)), Helpers.oneu32)
     else
       ECons (cons, args)

   method! efield env _ e f =
     (* A field destructor must dereference. *)
     let e = self#visit env e in
     if is_mutual_type mutual_map e.typ then
       EField (with_type (assert_tbuf e.typ) (EBufRead (e, Helpers.zerou32)), f)
     else
       EField (e, f) *)
end

 let flatten_mutual map : decl -> decl list =
 function
   | DTypeMutual type_decls ->
    let decls = List.fold_right (fun ty_decl os ->
      match ty_decl with
      | DType(n, flags, arity, def, _) -> DType(n, flags, arity, def, true) :: os
      | _ -> assert false) type_decls [] in
    let name_tbl = Hashtbl.create 4 in
    let names = List.map (fun x ->
      match x with
      | DType(n, _, _, _, _) ->
        Hashtbl.add name_tbl n (); n
      | _ -> assert false) decls in
    List.iter (fun n -> Hashtbl.add map n name_tbl) names;
    decls
   | d -> [d]

 let remove_mutual_types files =
  let map = Hashtbl.create 43 in
  let files' = List.map (fun (file, ds) -> (file, KList.map_flatten (flatten_mutual map) ds)) files in
  visit_files () (mutual_behind_ptr map) files'
