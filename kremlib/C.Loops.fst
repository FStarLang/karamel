(** This modules exposes a series of combinators; they are modeled using
 * higher-order functions and specifications, and extracted, using a
 * meta-theoretic argument, to actual C loops. *)
module C.Loops

open FStar.ST
open FStar.Buffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module UInt32 = FStar.UInt32

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(** The functions in this module use the following convention:
 *  - the first arguments are buffers;
 *  - the destination buffer comes first, followed by the input buffer (as in
 *    C's memcpy)
 *  - each buffer is followed by its length; if several buffers share the same
 *    length, there is a single length argument after the buffers
 *  - the function-specific arguments come next (e.g. the number of times one
 *    may want to call the function in [repeat])
 *  - the second to last argument is the loop invariant (which may have
 *    dependencies on all the parameters before)
 *  - the last argument is the loop body (that will depend on the invariant, and
 *    possibly all the other parameters before. *)


(* Generic-purpose for-loop combinators ***************************************)

(* Currently extracting as:
    for (int i = <start>; i != <finish>; ++i)
      <f> i;
*)
val for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish >= UInt32.v start} ->
  inv:(HS.mem -> nat -> Type0) ->
  f:(i:UInt32.t{UInt32.(v start <= v i /\ v i < v finish)} -> Stack unit
                        (requires (fun h -> inv h (UInt32.v i)))
                        (ensures (fun h_1 _ h_2 -> UInt32.(inv h_1 (v i) /\ inv h_2 (v i + 1)))) ) ->
  Stack unit
    (requires (fun h -> inv h (UInt32.v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (UInt32.v finish)))
let rec for start finish inv f =
  if start = finish then
    ()
  else begin
    f start;
    for (UInt32.(start +^ 1ul)) finish inv f
  end

(* To be extracted as:
    for (int i = <start>; i != <finish>; --i)
      <f> i;
*)
val reverse_for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish <= UInt32.v start} ->
  inv:(HS.mem -> nat -> Type0) ->
  f:(i:UInt32.t{UInt32.(v start >= v i /\ v i > v finish)} -> Stack unit
                        (requires (fun h -> inv h (UInt32.v i)))
                        (ensures (fun h_1 _ h_2 -> UInt32.(inv h_1 (v i) /\ inv h_2 (v i - 1)))) ) ->
  Stack unit
    (requires (fun h -> inv h (UInt32.v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (UInt32.v finish)))
let rec reverse_for start finish inv f =
  if start = finish then
    ()
  else begin
    f start;
    reverse_for (UInt32.(start -^ 1ul)) finish inv f
  end

(* To be extracted as:
    int i = <start>;
    bool b = false;
    for (; (!b) && (i != <end>); ++i) {
      b = <f> i;
    }
    // i and b must be in scope after the loop
*)
val interruptible_for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish >= UInt32.v start} ->
  inv:(HS.mem -> nat -> bool -> GTot Type0) ->
  f:(i:UInt32.t{UInt32.(v start <= v i /\ v i < v finish)} -> Stack bool
                        (requires (fun h -> inv h (UInt32.v i) false))
                        (ensures (fun h_1 b h_2 -> inv h_1 (UInt32.v i) false /\ inv h_2 UInt32.(v i + 1) b)) ) ->
  Stack (UInt32.t * bool)
    (requires (fun h -> inv h (UInt32.v start) false))
    (ensures (fun _ res h_2 -> let (i, b) = res in ((if b then True else i == finish) /\ inv h_2 (UInt32.v i) b)))
let rec interruptible_for start finish inv f =
  if start = finish then
    (finish, false)
  else
    let start' = UInt32.(start +^ 1ul) in
    if f start
    then (start', true)
    else interruptible_for start' finish inv f

(* To be extracted as:
    int i = <start>;
    bool b = false;
    for (; (!b) && (i != <end>); --i) {
      b = <f> i;
    }
    // i and b must be in scope after the loop
*)
val interruptible_reverse_for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish <= UInt32.v start} ->
  inv:(HS.mem -> nat -> bool -> GTot Type0) ->
  f:(i:UInt32.t{UInt32.(v start >= v i /\ v i > v finish)} -> Stack bool
                        (requires (fun h -> inv h (UInt32.v i) false))
                        (ensures (fun h_1 b h_2 -> inv h_1 (UInt32.v i) false /\ inv h_2 UInt32.(v i - 1) b)) ) ->
  Stack (UInt32.t * bool)
    (requires (fun h -> inv h (UInt32.v start) false))
    (ensures (fun _ res h_2 -> let (i, b) = res in ((if b then True else i == finish) /\ inv h_2 (UInt32.v i) b)))
let rec interruptible_reverse_for start finish inv f =
  if start = finish then
    (finish, false)
  else
    let start' = UInt32.(start -^ 1ul) in
    if f start
    then (start', true)
    else interruptible_reverse_for start' finish inv f


(* Mapping the contents of a buffer into another ******************************)

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


(** Extracts as:
 * for (int i = 0; i < <l>; ++i)
 *   out[i] = <f>(in[i]);
 *)
inline_for_extraction
val map:
  #a:Type0 -> #b:Type0 ->
  output: buffer b ->
  input: buffer a{disjoint input output} ->
  l: UInt32.t{ UInt32.v l = Buffer.length output /\ UInt32.v l = Buffer.length input } ->
  f:(a -> Tot b) ->
  Stack unit
    (requires (fun h -> live h input /\ live h output ))
    (ensures (fun h_1 r h_2 -> modifies_1 output h_1 h_2 /\ live h_2 input /\ live h_1 input /\ live h_2 output
      /\ live h_2 output
      /\ (let s1 = as_seq h_1 input in
         let s2 = as_seq h_2 output in
         s2 == seq_map f s1) ))
inline_for_extraction
let map #a #b output input l f =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 output /\ live h1 input /\ modifies_1 output h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). {:pattern (get h1 output j)} (j >= i /\ j < UInt32.v l) ==> get h1 output j == get h0 output j)
    /\ (forall (j:nat). {:pattern (get h1 output j)} j < i ==> get h1 output j == f (get h0 input j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    output.(i) <- f (input.(i))
  in
  for 0ul l inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 output) (seq_map f (as_seq h0 input))


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


(** Extracts as:
 * for (int i = 0; i < <l>; ++i)
 *   out[i] = <f>(in1[i], in2[i]);
 *)
val map2:
  #a:Type0 -> #b:Type0 -> #c:Type0 ->
  output: buffer c ->
  in1: buffer a{disjoint output in1} -> in2: buffer b{disjoint output in2} ->
  l: UInt32.t{ UInt32.v l = Buffer.length output /\ UInt32.v l = Buffer.length in1
     /\ UInt32.v l = Buffer.length in2 } ->
  f:(a -> b -> Tot c) ->
  Stack unit
    (requires (fun h -> live h in1 /\ live h in2 /\ live h output ))
    (ensures (fun h_1 r h_2 -> modifies_1 output h_1 h_2 /\ live h_2 in1 /\ live h_2 in2
      /\ live h_1 in1 /\ live h_1 in2 /\ live h_2 output
      /\ (let s1 = as_seq h_1 in1 in
         let s2 = as_seq h_1 in2 in
         let s = as_seq h_2 output in
         s == seq_map2 f s1 s2) ))
let map2 #a #b #c output in1 in2 l f =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 output /\ live h1 in1 /\ live h1 in2 /\ modifies_1 output h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). {:pattern (get h1 output j)} (j >= i /\ j < UInt32.v l) ==> get h1 output j == get h0 output j)
    /\ (forall (j:nat). {:pattern (get h1 output j)} j < i ==> get h1 output j == f (get h0 in1 j) (get h0 in2 j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    output.(i) <- f (in1.(i)) (in2.(i))
  in
  for 0ul l inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 output) (seq_map2 f (as_seq h0 in1) (as_seq h0 in2))


(** Extracts as:
 * for (int i = 0; i < <l>; ++i)
 *   b[i] = <f>(b[i]);
 *)
val in_place_map:
  #a:Type0 ->
  b: buffer a ->
  l: UInt32.t{ UInt32.v l = Buffer.length b } ->
  f:(a -> Tot a) ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h_1 r h_2 -> modifies_1 b h_1 h_2 /\ live h_2 b /\ live h_1 b
      /\ (let s1 = as_seq h_1 b in
         let s2 = as_seq h_2 b in
         s2 == seq_map f s1) ))
let in_place_map #a b l f =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 b /\ modifies_1 b h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). {:pattern (get h1 b j)} (j >= i /\ j < UInt32.v l) ==> get h1 b j == get h0 b j)
    /\ (forall (j:nat). {:pattern (get h1 b j)} j < i ==> get h1 b j == f (get h0 b j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    b.(i) <- f (b.(i))
  in
  for 0ul l inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 b) (seq_map f (as_seq h0 b))


(** Extracts as (destination buffer comes first):
 * for (int i = 0; i < <l>; ++i)
 *   in1[i] = <f>(in1[i], in2[i]);
 *)
val in_place_map2:
  #a:Type0 -> #b:Type0 ->
  in1: buffer a ->
  in2: buffer b{disjoint in1 in2} ->
  l: UInt32.t{ UInt32.v l = Buffer.length in1 /\ UInt32.v l = Buffer.length in2} ->
  f:(a -> b -> Tot a) ->
  Stack unit
    (requires (fun h -> live h in1 /\ live h in2))
    (ensures (fun h_1 r h_2 -> modifies_1 in1 h_1 h_2 /\ live h_2 in1 /\ live h_2 in2
      /\ live h_1 in1 /\ live h_1 in2
      /\ (let s1 = as_seq h_1 in1 in
         let s2 = as_seq h_1 in2 in
         let s = as_seq h_2 in1 in
         s == seq_map2 f s1 s2) ))
let in_place_map2 #a #b in1 in2 l f =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 in1 /\ live h1 in2 /\ modifies_1 in1 h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). {:pattern (get h1 in1 j)} (j >= i /\ j < UInt32.v l) ==> get h1 in1 j == get h0 in1 j)
    /\ (forall (j:nat). {:pattern (get h1 in1 j)} j < i ==> get h1 in1 j == f (get h0 in1 j) (get h0 in2 j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    in1.(i) <- f (in1.(i)) (in2.(i))
  in
  for 0ul l inv f';
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 in1) (seq_map2 f (as_seq h0 in1) (as_seq h0 in2))


#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"


(* Repeating the same operation a number of times over a buffer ***************)

val repeat_spec: #a:Type -> n:nat -> (f: a -> Tot a) -> a -> Tot a (decreases n)
let rec repeat_spec #a n f x = if n = 0 then x else repeat_spec (n-1) f (f x)

private
val lemma_repeat: #a:Type -> n:nat{n > 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (repeat_spec n f x == f (repeat_spec (n-1) f x))
let rec lemma_repeat #a n f x =
  if n = 1 then ()
  else lemma_repeat (n-1) f (f x)

private
val lemma_repeat_0: #a:Type -> n:nat{n = 0} -> f:( a -> Tot a) -> x:a -> Lemma
  (repeat_spec n f x == x)
let rec lemma_repeat_0 #a n f x = ()

(** To be extracted as:
 * for (int i = 0; i < n; ++i)
 *   f(b[i]);
 *)
val repeat:
  #a:Type0 ->
  #len:nat ->
  #f:(s:Seq.seq a{Seq.length s = len} -> Tot (s':Seq.seq a{Seq.length s' = Seq.length s})) ->
  b: buffer a ->
  l: UInt32.t{ UInt32.v l = Buffer.length b /\ UInt32.v l = len } ->
  n:UInt32.t ->
  f':(b:buffer a{length b = len} -> Stack unit
                     (requires (fun h -> live h b))
                     (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ modifies_1 b h0 h1
                       /\ (let b0 = as_seq h0 b in
                          let b1 = as_seq h1 b in
                          b1 == f b0)))) ->
  Stack unit
    (requires (fun h -> live h b ))
    (ensures (fun h_1 r h_2 -> modifies_1 b h_1 h_2 /\ live h_1 b /\ live h_2 b
      /\ (let s = as_seq h_1 b in
         let s' = as_seq h_2 b in
         s' == repeat_spec (UInt32.v n) f s) ))
let repeat #a #len #f b l max fc =
  let h0 = ST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 b /\ modifies_1 b h0 h1 /\ i <= UInt32.v max
    /\ as_seq h1 b == repeat_spec i f (as_seq h0 b)
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v max ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    fc b;
    lemma_repeat (UInt32.v i + 1) f (as_seq h0 b)
  in
  lemma_repeat_0 0 f (as_seq h0 b);
  for 0ul max inv f'
