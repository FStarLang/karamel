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

val repeat_spec: #a:Type -> n:nat -> (f: a -> Tot a) -> a -> Tot a (decreases n)
let rec repeat_spec #a n f x = if n = 0 then x else repeat_spec (n-1) f (f x)

#reset-options "--initial_fuel 2 --max_fuel 2"

val lemma_repeat: #a:Type -> n:nat{n > 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (repeat_spec n f x == f (repeat_spec (n-1) f x))
let rec lemma_repeat #a n f x =
  if n = 1 then ()
  else lemma_repeat (n-1) f (f x)

val lemma_repeat_0: #a:Type -> n:nat{n = 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (repeat_spec n f x == x)
let rec lemma_repeat_0 #a n f x = ()

#reset-options "--max_fuel 0"

val repeat_range_spec: #a:Type -> min:nat -> max:nat{min <= max} -> f:(a -> i:nat{i < max} -> Tot a) ->
  x:a -> Tot a (decreases (max - min))
let rec repeat_range_spec #a min max f x =
  if min = max then x
  else repeat_range_spec (min+1) max f (f x min)

#reset-options "--initial_fuel 1 --max_fuel 1"

val lemma_repeat_range_0: #a:Type -> min:nat -> max:nat{min <= max} -> f:(a -> i:nat{i < max} -> Tot a) -> x:a ->
  Lemma (requires (min = max))
        (ensures (repeat_range_spec min max f x == x))
let lemma_repeat_range_0 #a min max f x = ()

val lemma_repeat_range_1: #a:Type -> min:nat -> max:nat{min <= max} -> f:(a -> i:nat{i < max} -> Tot a) -> x:a ->
  Lemma (requires (min <> max))
        (ensures (min <> max /\ repeat_range_spec (min+1) max f (f x min) == repeat_range_spec min max f x))
let lemma_repeat_range_1 #a min max f x = ()

#reset-options "--initial_fuel 2 --max_fuel 2"

val lemma_repeat_range_spec:
  #a:Type -> min:nat -> max:nat{min < max} -> f:(a -> i:nat{i < max} -> Tot a) -> x:a -> 
  Lemma (requires (True))
        (ensures f (repeat_range_spec min (max-1) f x) (max-1) == repeat_range_spec min max f x)
        (decreases (max - min))
let rec lemma_repeat_range_spec #a min max f x =
  if min = max - 1 then ()
  else lemma_repeat_range_spec (min+1) max f (f x min)

#reset-options "--max_fuel 0"
