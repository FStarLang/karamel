(* Rust-specific transformations *)

open Ast

(* Doesn't make sense in Rust *)
let remove_push_pop_frame = object
  inherit [_] map
  method! visit_EPushFrame _ = EUnit
  method! visit_EPopFrame _ = EUnit
end

(* Local aliases create opportunities for move-outs of arrays, which then renders the moved-out
   variable unusable in Rust. As a systematic rewriting, we inline away `let x = y` when `y` is a
   non-copyable type (such as, arrays). *)

let remove_aliases = object (self)
  inherit [_] map

  method! visit_ELet env b e1 e2 =
    let e1 = self#visit_expr env e1 in
    let e2 = self#visit_expr env e2 in
    let is_non_copyable = function
      | TBuf _ | TArray _ -> `Definitely
      | _ -> `Unclear
    in
    match e1.node with
    | EBound _ when is_non_copyable b.typ = `Definitely ->
        (DeBruijn.subst e1 0 e2).node
    | EBufSub ({ node = EBound _; _ } as e1, { node = EConstant (_, "0"); _ }) when is_non_copyable b.typ = `Definitely ->
        (DeBruijn.subst e1 0 e2).node
    | _ ->
        ELet (b, e1, e2)
end

let simplify files =
  let files = remove_push_pop_frame#visit_files () files in
  let files = remove_aliases#visit_files () files in
  files
