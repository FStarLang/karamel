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
    Seq.empty
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
  if Seq.length s = 0 then Seq.empty
  else
    let s'' = Seq.cons (f (Seq.head s) (Seq.head s')) (seq_map2 f (Seq.tail s) (Seq.tail s')) in
    s''

val repeat: #a:Type -> n:nat -> (f: a -> Tot a) -> a -> Tot a (decreases n)
let rec repeat #a n f x =
  if n = 0 then x else repeat (n-1) f (f x)

#reset-options "--initial_fuel 2 --max_fuel 2"

val repeat_induction: #a:Type -> n:nat{n > 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (repeat n f x == f (repeat (n-1) f x))
let rec repeat_induction #a n f x =
  if n = 1 then ()
  else repeat_induction (n-1) f (f x)

val repeat_base: #a:Type -> n:nat{n = 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (repeat n f x == x)
let rec repeat_base #a n f x = ()

#reset-options "--max_fuel 0"

val repeat_range: #a:Type -> min:nat -> max:nat{min <= max} -> f:(a -> i:nat{i < max} -> Tot a) ->
  x:a -> Tot a (decreases (max - min))
let rec repeat_range #a min max f x =
  if min = max then x
  else repeat_range (min+1) max f (f x min)

#reset-options "--initial_fuel 1 --max_fuel 1"

val repeat_range_base: #a:Type -> min:nat -> f:(a -> i:nat{i < min} -> Tot a) -> x:a ->
  Lemma (ensures (repeat_range min min f x == x))
let repeat_range_base #a min f x = ()

#reset-options "--initial_fuel 2 --max_fuel 2"

val repeat_range_induction:
  #a:Type -> min:nat -> max:nat{min < max} -> f:(a -> i:nat{i < max} -> Tot a) -> x:a -> 
  Lemma (requires (True))
        (ensures f (repeat_range min (max-1) f x) (max-1) == repeat_range min max f x)
        (decreases (max - min))
let rec repeat_range_induction #a min max f x =
  if min = max - 1 then ()
  else repeat_range_induction (min+1) max f (f x min)

#reset-options "--max_fuel 0"

[@(deprecated "Spec.Loops.repeat")]
unfold
let repeat_spec = repeat
[@(deprecated "Spec.Loops.repeat_base")]
unfold
let lemma_repeat_0 = repeat_base
[@(deprecated "Spec.Loops.repeat_induction")]
unfold
let lemma_repeat = repeat_induction

[@(deprecated "Spec.Loops.repeat_range")]
unfold
let repeat_range_spec = repeat_range
[@(deprecated "Spec.Loops.repeat_range_base")]
unfold
let lemma_repeat_range_0 = repeat_range_base
[@(deprecated "Spec.Loops.repeat_range_induction")]
unfold
let lemma_repeat_range_spec = repeat_range_induction
