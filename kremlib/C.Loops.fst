module C.Loops

(* This modules exposes a series of combinators; they are modeled using
 * higher-order functions and specifications, and extracted, using a
 * meta-theoretic argument, to actual C loops. *)

open FStar.ST
open FStar.Buffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module UInt32 = FStar.UInt32

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(* To be extracted as:
  {
    int i = <start>;
    for (; i != <finish>; ++i) <f>;
  }
  // i need not be in scope after the loop
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
  {
    int i = <start>;
    for (; i != <finish>; --i) <f>;
  }
  // i need not be in scope after the loop
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
    for (; b || (i != <end>); ++i) {
      b = <f>;
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
    for (; b || (i != <end>); --i) {
      b = <f>;
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
