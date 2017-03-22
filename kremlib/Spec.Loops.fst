module Spec.Loops

#reset-options "--max_fuel 0"

val seq_map:
  #a:Type -> #b:Type ->
  f:(a -> Tot b) ->
  s:Seq.seq a ->
  Tot (s':Seq.seq b{Seq.length s = Seq.length s' /\
    (forall (i:nat). {:pattern (Seq.index s' i)} i < Seq.length s' ==> Seq.index s' i == f (Seq.index s i))})
    (decreases (Seq.length s))
let rec seq_map #a #b f s =
  if Seq.length s = 0 then
    Seq.createEmpty
  else
    let s' = Seq.cons (f (Seq.head s)) (seq_map f (Seq.tail s)) in
    s'


val seq_map2:
  #a:Type -> #b:Type -> #c:Type ->
  f:(a -> b -> Tot c) ->
  s:Seq.seq a -> s':Seq.seq b{Seq.length s = Seq.length s'} ->
  Tot (s'':Seq.seq c{Seq.length s = Seq.length s'' /\
    (forall (i:nat). {:pattern (Seq.index s'' i)} i < Seq.length s'' ==> Seq.index s'' i == f (Seq.index s i) (Seq.index s' i))})
    (decreases (Seq.length s))
let rec seq_map2 #a #b #c f s s' =
  if Seq.length s = 0 then Seq.createEmpty
  else
    let s'' = Seq.cons (f (Seq.head s) (Seq.head s')) (seq_map2 f (Seq.tail s) (Seq.tail s')) in
    s''

val repeat_spec: #a:Type -> n:nat -> (f: a -> Tot a) -> a -> Tot a (decreases n)
let rec repeat_spec #a n f x = if n = 0 then x else repeat_spec (n-1) f (f x)

val lemma_repeat: #a:Type -> n:nat{n > 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (repeat_spec n f x == f (repeat_spec (n-1) f x))
let rec lemma_repeat #a n f x =
  if n = 1 then ()
  else lemma_repeat (n-1) f (f x)

val lemma_repeat_0: #a:Type -> n:nat{n = 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (repeat_spec n f x == x)
let rec lemma_repeat_0 #a n f x = ()
