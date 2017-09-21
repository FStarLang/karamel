module MutualDatatypesPolyIndex

open TestLib

#set-options "--lax"

[@Gc] type tree (a : Type0) =
| Node : a -> tree_list a -> tree a
| Empty : tree a
and tree_list (a : Type0) =
| Nil : tree_list a
| Cons : tree a -> tree_list a -> tree_list a

let rec fill (#a:Type0) (width:int) (t : tree a) : Tot (tree_list a) (decreases width) =
if width = 0
then Nil
else Cons t (fill (width - 1) t)

let rec mk_tree (#a:Type0) (def:a) (height:int) : Tot (tree a) (decreases height) =
  match height with
  | 0 -> Empty
  | n -> Node def (mk_tree_list def (n - 1))
and mk_tree_list (#a:Type0) (def:a) (height:int)  : Tot (tree_list a) (decreases height) =
   fill 10 (mk_tree def height)

let rec height (#a:Type0) : tree a -> int =
function
| Empty -> 0
| Node _ cs -> 1 + max_child_height 0 cs
and max_child_height (#a:Type0) (max : int) : tree_list a -> int =
function
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
