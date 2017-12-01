(* A thin layer on top of François' visitors. *)

open Ast

class ['self] map = object (self: 'self)

  inherit [_] Ast.map

  method! visit_with_type: 'node 'ret.
    (_ -> 'node -> 'ret) -> _ -> 'node with_type -> 'ret with_type =
    fun f (env, _) x ->
      let typ = self#visit_typ (env, None) x.typ in
      let node = f (env, Some typ) x.node in
      { node; typ }

end

class ['self] iter = object (self: 'self)

  inherit [_] Ast.iter

  method! visit_with_type: 'node.
    (('env * typ option) -> 'node -> unit) -> ('env * typ option) -> 'node with_type -> unit =
    fun f (env, _) x ->
      f (env, Some x.typ) x.node

end
