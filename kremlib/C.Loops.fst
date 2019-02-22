(* This module exposes a series of combinators; they are modeled using
 * higher-order functions and specifications, and extracted, using a
 * meta-theoretic argument, to actual C loops. *)
module C.Loops

open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module UInt32 = FStar.UInt32
module UInt64 = FStar.UInt64

include Spec.Loops

module Buffer = LowStar.Buffer

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

(* These combinators enjoy first-class support in KreMLin. (See [combinators] in
 * src/Simplify.ml *)

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

val for64:
  start:UInt64.t ->
  finish:UInt64.t{UInt64.v finish >= UInt64.v start} ->
  inv:(HS.mem -> nat -> Type0) ->
  f:(i:UInt64.t{UInt64.(v start <= v i /\ v i < v finish)} -> Stack unit
                        (requires (fun h -> inv h (UInt64.v i)))
                        (ensures (fun h_1 _ h_2 -> UInt64.(inv h_1 (v i) /\ inv h_2 (v i + 1)))) ) ->
  Stack unit
    (requires (fun h -> inv h (UInt64.v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (UInt64.v finish)))
let rec for64 start finish inv f =
  if start = finish then
    ()
  else begin
    f start;
    for64 (UInt64.(start +^ 1UL)) finish inv f
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
    bool b = false;
    int i = <start>;
    for (; (!b) && (i != <end>); ++i) {
      b = <f> i;
    }
    (i, b)
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
    while (true) {
      bool b = <f> i;
      if (b) {
         break;
      }
    }
*)
val do_while:
  inv:(HS.mem -> bool -> GTot Type0) ->
  f:(unit -> Stack bool
            (requires (fun h -> inv h false))
            (ensures (fun h_1 b h_2 -> inv h_1 false /\ inv h_2 b)) ) ->
  Stack unit
    (requires (fun h -> inv h false))
    (ensures (fun _ _ h_2 -> inv h_2 true))
let rec do_while inv f =
  if not (f ()) then
    do_while inv f


(* Extracted as:
   while (test ()) {
     body ();
   }
*)
val while:
  #test_pre: (HS.mem -> GTot Type0) ->
  #test_post: (bool -> HS.mem -> GTot Type0) ->
  $test: (unit -> Stack bool
    (requires (fun h -> test_pre h))
    (ensures (fun h0 x h1 -> test_post x h1))) ->
  body: (unit -> Stack unit
    (requires (fun h -> test_post true h))
    (ensures (fun h0 _ h1 -> test_pre h1))) ->
  Stack unit
    (requires (fun h -> test_pre h))
    (ensures (fun h0 _ h1 -> test_post false h1))
let rec while #test_pre #test_post test body =
  if test () then begin
    body ();
    while #test_pre #test_post test body
  end


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


(* Non-primitive combinators that can be expressed in terms of the above ******)

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
    (ensures (fun h_1 r h_2 -> modifies (loc_buffer output) h_1 h_2 /\ live h_2 input /\ live h_1 input /\ live h_2 output
      /\ live h_2 output
      /\ (let s1 = as_seq h_1 input in
         let s2 = as_seq h_2 output in
         s2 == seq_map f s1) ))
inline_for_extraction
let map #a #b output input l f =
  let h0 = HST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 output /\ live h1 input /\ modifies (loc_buffer output) h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). (j >= i /\ j < UInt32.v l) ==> get h1 output j == get h0 output j)
    /\ (forall (j:nat). j < i ==> get h1 output j == f (get h0 input j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    let xi = input.(i) in
    output.(i) <- f xi
  in
  for 0ul l inv f';
  let h1 = HST.get() in
  Seq.lemma_eq_intro (as_seq h1 output) (seq_map f (as_seq h0 input))


(** Extracts as:
 * for (int i = 0; i < <l>; ++i)
 *   out[i] = <f>(in1[i], in2[i]);
 *)
inline_for_extraction
val map2:
  #a:Type0 -> #b:Type0 -> #c:Type0 ->
  output: buffer c ->
  in1: buffer a{disjoint output in1} -> in2: buffer b{disjoint output in2} ->
  l: UInt32.t{ UInt32.v l = Buffer.length output /\ UInt32.v l = Buffer.length in1
     /\ UInt32.v l = Buffer.length in2 } ->
  f:(a -> b -> Tot c) ->
  Stack unit
    (requires (fun h -> live h in1 /\ live h in2 /\ live h output ))
    (ensures (fun h_1 r h_2 -> modifies (loc_buffer output) h_1 h_2 /\ live h_2 in1 /\ live h_2 in2
      /\ live h_1 in1 /\ live h_1 in2 /\ live h_2 output
      /\ (let s1 = as_seq h_1 in1 in
         let s2 = as_seq h_1 in2 in
         let s = as_seq h_2 output in
         s == seq_map2 f s1 s2) ))
inline_for_extraction
let map2 #a #b #c output in1 in2 l f =
  let h0 = HST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 output /\ live h1 in1 /\ live h1 in2 /\ modifies (loc_buffer output) h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). (j >= i /\ j < UInt32.v l) ==> get h1 output j == get h0 output j)
    /\ (forall (j:nat). j < i ==> get h1 output j == f (get h0 in1 j) (get h0 in2 j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    let xi = in1.(i) in
    let yi = in2.(i) in
    output.(i) <- f xi yi
  in
  for 0ul l inv f';
  let h1 = HST.get() in
  Seq.lemma_eq_intro (as_seq h1 output) (seq_map2 f (as_seq h0 in1) (as_seq h0 in2))


(** Extracts as:
 * for (int i = 0; i < <l>; ++i)
 *   b[i] = <f>(b[i]);
 *)
inline_for_extraction
val in_place_map:
  #a:Type0 ->
  b: buffer a ->
  l: UInt32.t{ UInt32.v l = Buffer.length b } ->
  f:(a -> Tot a) ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h_1 r h_2 -> modifies (loc_buffer b) h_1 h_2 /\ live h_2 b /\ live h_1 b
      /\ (let s1 = as_seq h_1 b in
         let s2 = as_seq h_2 b in
         s2 == seq_map f s1) ))
inline_for_extraction
let in_place_map #a b l f =
  let h0 = HST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 b /\ modifies (loc_buffer b) h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). (j >= i /\ j < UInt32.v l) ==> get h1 b j == get h0 b j)
    /\ (forall (j:nat). j < i ==> get h1 b j == f (get h0 b j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    let xi = b.(i) in
    b.(i) <- f xi
  in
  for 0ul l inv f';
  let h1 = HST.get() in
  Seq.lemma_eq_intro (as_seq h1 b) (seq_map f (as_seq h0 b))


(** Extracts as (destination buffer comes first):
 * for (int i = 0; i < <l>; ++i)
 *   in1[i] = <f>(in1[i], in2[i]);
 *)
inline_for_extraction
val in_place_map2:
  #a:Type0 -> #b:Type0 ->
  in1: buffer a ->
  in2: buffer b{disjoint in1 in2} ->
  l: UInt32.t{ UInt32.v l = Buffer.length in1 /\ UInt32.v l = Buffer.length in2} ->
  f:(a -> b -> Tot a) ->
  Stack unit
    (requires (fun h -> live h in1 /\ live h in2))
    (ensures (fun h_1 r h_2 -> modifies (loc_buffer in1) h_1 h_2 /\ live h_2 in1 /\ live h_2 in2
      /\ live h_1 in1 /\ live h_1 in2
      /\ (let s1 = as_seq h_1 in1 in
         let s2 = as_seq h_1 in2 in
         let s = as_seq h_2 in1 in
         s == seq_map2 f s1 s2) ))
inline_for_extraction
let in_place_map2 #a #b in1 in2 l f =
  let h0 = HST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 in1 /\ live h1 in2 /\ modifies (loc_buffer in1) h0 h1 /\ i <= UInt32.v l
    /\ (forall (j:nat). (j >= i /\ j < UInt32.v l) ==> get h1 in1 j == get h0 in1 j)
    /\ (forall (j:nat). j < i ==> get h1 in1 j == f (get h0 in1 j) (get h0 in2 j))
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    let xi = in1.(i) in
    let yi = in2.(i) in
    in1.(i) <- f xi yi
  in
  for 0ul l inv f';
  let h1 = HST.get() in
  Seq.lemma_eq_intro (as_seq h1 in1) (seq_map2 f (as_seq h0 in1) (as_seq h0 in2))


#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"


(* Repeating the same operation a number of times over a buffer ***************)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(** To be extracted as:
 * for (int i = 0; i < n; ++i)
 *   f(b);
 *)
inline_for_extraction
val repeat:
  #a:Type0 ->
  l: UInt32.t ->
  f:(s:Seq.seq a{Seq.length s = UInt32.v l} ->
    Tot (s':Seq.seq a{Seq.length s' = Seq.length s})) ->
  b: buffer a{Buffer.length b = UInt32.v l} ->
  max:UInt32.t ->
  fc:(b:buffer a{length b = UInt32.v l} ->
    Stack unit
      (requires (fun h -> live h b))
      (ensures (fun h0 _ h1 ->
        live h0 b /\ live h1 b /\ modifies (loc_buffer b) h0 h1 /\ (
        let b0 = as_seq h0 b in
        let b1 = as_seq h1 b in
        b1 == f b0)))) ->
  Stack unit
    (requires (fun h -> live h b ))
    (ensures (fun h_1 r h_2 ->
      modifies (loc_buffer b) h_1 h_2 /\ live h_1 b /\ live h_2 b /\ (
      let s = as_seq h_1 b in
      let s' = as_seq h_2 b in
      s' == Spec.Loops.repeat (UInt32.v max) f s) ))

inline_for_extraction
let repeat #a l f b max fc =
  let h0 = HST.get() in
  let inv (h1: HS.mem) (i: nat): Type0 =
    live h1 b /\ modifies (loc_buffer b) h0 h1 /\ i <= UInt32.v max
    /\ as_seq h1 b == Spec.Loops.repeat i f (as_seq h0 b)
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v max ) }): Stack unit
    (requires (fun h -> inv h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  =
    fc b;
    Spec.Loops.repeat_induction (UInt32.v i + 1) f (as_seq h0 b)
  in
  Spec.Loops.repeat_base 0 f (as_seq h0 b);
  for 0ul max inv f'


(** Implementation of Spec.Loops.repeat_range *)

(** The type of the specification of the loop body (the function f
    given to Spec.Loops.repeat_range *)
    
inline_for_extraction
let repeat_range_body_spec
  (a: Type0)
  (max: nat)
: Tot Type
= (a -> i:nat{i < max} -> Tot a)

(** The type of the semantics (interpretation) of a memory state as a
    value of the type `a` of the high-level state on which the loop
    body specification operates *)

inline_for_extraction
let repeat_range_body_interp
  (a: Type0)
  (inv: (HS.mem -> GTot Type0))
: Tot Type
= (h: HS.mem { inv h } ) ->
  GTot a

(** The type of the implementation of the loop body, proven correct
    with respect to the corresponding specification `f` *)

inline_for_extraction
let repeat_range_body_impl
  (#a:Type0)
  (min:UInt32.t)
  (max:UInt32.t{UInt32.v min <= UInt32.v max})
  (f: Ghost.erased (repeat_range_body_spec a (UInt32.v max)))
  (inv: (HS.mem -> GTot Type0))
  (interp: repeat_range_body_interp a inv)
: Tot Type
= (i:UInt32.t{UInt32.v min <= UInt32.v i /\ UInt32.v i < UInt32.v max}) ->
  HST.Stack unit
  (requires (fun h -> inv h))
  (ensures (fun h0 _ h1 ->
    inv h0 /\ inv h1 /\
    interp h1 == (Ghost.reveal f) (interp h0) (UInt32.v i)
  ))

(** The implementation of the actual loop
 
   To be extracted as:
    for (int i = min; i < max; ++i)
    f(b, i);

   This combinator is generic. Typically, the interpretation reads the
   contents of a few objects (buffers, references, etc.), and the
   invariant contains a modifies clause that asserts that only those
   objects are modified, and that they are live.
 *)

inline_for_extraction
val repeat_range:
  #a:Type0 ->
  min:UInt32.t ->
  max:UInt32.t{UInt32.v min <= UInt32.v max} ->
  f: (Ghost.erased (repeat_range_body_spec a (UInt32.v max))) ->
  inv: (HS.mem -> GTot Type0) ->
  interp: repeat_range_body_interp a inv ->
  fc: repeat_range_body_impl min max f inv interp ->
  HST.Stack unit
    (requires (fun h -> inv h))
    (ensures (fun h_1 _ h_2 ->
      inv h_1 /\ inv h_2 /\
      interp h_2 == Spec.Loops.repeat_range (UInt32.v min) (UInt32.v max) (Ghost.reveal f) (interp h_1)
    ))

inline_for_extraction
let repeat_range #a min max f inv interp fc =
  let h0 = HST.get() in
  let inv' (h1: HS.mem) (i: nat): Type0 =
    inv h1 /\
    i <= UInt32.v max /\ UInt32.v min <= i /\
    interp h1 == Spec.Loops.repeat_range (UInt32.v min) i (Ghost.reveal f) (interp h0)
  in
  let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v max ) }): HST.Stack unit
    (requires (fun h -> inv' h (UInt32.v i)))
    (ensures (fun h_1 _ h_2 -> UInt32.(inv' h_2 (v i + 1))))
  =
    fc i;
    Spec.Loops.repeat_range_induction (UInt32.v min) (UInt32.v i + 1) (Ghost.reveal f) (interp h0)
  in
  Spec.Loops.repeat_range_base (UInt32.v min) (Ghost.reveal f) (interp h0);
  for min max inv' f'


let rec total_while_gen
  (#t: Type)
  (tmes: (t -> GTot lex_t))
  (tinv: (bool -> t -> GTot Type0))
  (tcontinue: (t -> Tot bool))
  (body:
    (x: t) ->
    Pure t
    (requires (tinv true x))
    (ensures (fun y ->
      tinv (tcontinue y) y /\ (
      if tcontinue y then tmes y << tmes x else True)
    )))
  (x: t)
: Pure t
  (requires (tinv true x))
  (ensures (fun y -> tinv false y))
  (decreases (tmes x))
= let y = body x in
  let continue = tcontinue y in
  if continue
  then total_while_gen tmes tinv tcontinue body y
  else y

inline_for_extraction
let total_while
  (#t: Type)
  (tmes: (t -> GTot nat))
  (tinv: (bool -> t -> GTot Type0))
  (body:
    (x: t) ->
    Pure (bool * t)
    (requires (tinv true x))
    (ensures (fun (continue, y) ->
      tinv continue y /\ (
      if continue then tmes y < tmes x else True)
    )))
  (x: t)
: Pure t
  (requires (tinv true x))
  (ensures (fun y -> tinv false y))
  (decreases (tmes x))
= let (_, res) =
    total_while_gen
      (fun (_, x) -> LexCons (tmes x) LexTop)
      (fun b (b_, x) -> b == b_ /\ tinv b x)
      (fun (x, _) -> x)
      (fun (_, x) -> body x)
      (true, x)
  in
  res
