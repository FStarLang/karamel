module MutualDatatypesPolyIndex

open TestLib

[@Gc] type tree (a : Type0) =
| Node : a -> tree_list a -> tree a
| Empty : tree a
and tree_list (a : Type0) =
| Nil : tree_list a
| Cons : tree a -> tree_list a -> tree_list a

let rec fill (#a:Type0) (width:nat) (t : tree a) : Tot (tree_list a) (decreases width) =
match width with
| 0 -> Nil
| _ ->
  Cons t (fill (width - 1) t)

let rec mk_tree (#a:Type0) (def:a) (height: nat) : Tot (tree a) (decreases %[height;0]) =
  match height with
  | 0 -> Empty
  | _ -> Node def (mk_tree_list def (height - 1))
and mk_tree_list (#a:Type0) (def:a) (height:nat) : Tot (tree_list a) (decreases %[height;1]) =
   let t = mk_tree def height
   in fill 1 t

let rec height (#a:Type0) (t:tree a): Tot nat (decreases t) =
match t with
| Empty -> 0
| Node _ cs -> 1 + max_child_height 0 cs
and max_child_height (#a:Type0) (max:nat) (tl:tree_list a) : Tot nat (decreases tl) =
match tl with
| Nil -> max
| Cons t ts ->
  let h = height t in
  if h > max
  then max_child_height h ts
  else max_child_height max ts

let main () =
  let t = mk_tree 1 10 in
  let h = height t in
  checku32 10ul (UInt32.uint_to_t h);
  C.exit_success
