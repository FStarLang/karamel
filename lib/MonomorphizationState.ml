open Ast
type node = lident * typ list * cg list
type color = Gray | Black
let state: (node, color * lident) Hashtbl.t = Hashtbl.create 41

let resolve t: typ =
  match t with
  | TApp _ | TCgApp _ when Hashtbl.mem state (flatten_tapp t) ->
      TQualified (snd (Hashtbl.find state (flatten_tapp t)))
  | TTuple ts when Hashtbl.mem state (tuple_lid, ts, []) ->
      TQualified (snd (Hashtbl.find state (tuple_lid, ts, [])))
  | _ ->
      t

let resolve_deep = (object(self)
  inherit [_] map

  method! visit_TApp () t ts =
    let ts = List.map (self#visit_typ ()) ts in
    resolve (TApp (t, ts))

  method! visit_TCgApp () t ts =
    resolve (TCgApp (t, ts))

  method! visit_TTuple () ts =
    let ts = List.map (self#visit_typ ()) ts in
    resolve (TTuple ts)
end)#visit_typ ()
