/// Main implementation file
/// ========================

module Impl.Bignum

/// These are the somewhat standard names across a lot of code for module
/// abbreviations. Sticking to them is good!
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq

module U32 = FStar.UInt32
module U64 = FStar.UInt64

/// I oftentimes use ``Spec`` to refer to the spec of the current module.
module Spec = Spec.Bignum

/// This module only contains operators, and is meant to be opened.
open LowStar.BufferOps
open FStar.HyperStack.ST

open Impl.Bignum.Lemmas

/// Try disabling this to see how much slower things get.
#set-options "--fuel 0 --ifuel 0"

/// Since bignums in our toy example have a variable length, we have to keep
/// track of this length at runtime. Using pairs in Low* is supported; since
/// pairs are values in F*, they are compiled to values in C, and end up as
/// structures passed by value. We'll see how to minimize allocation of
/// temporary structs as we go.
type t = U32.t & B.buffer U32.t

/// It's good to structure the code around an invariant. Since this is a
/// stateful representation, the invariant takes a memory. Note that the memory
/// comes first, as in the ``live`` predicate.
let invariant (h: HS.mem) (x: t) =
  let l, b = x in
  B.length b == U32.v l /\
  B.live h b

/// I find a small helper like this to be helpful.
let as_seq (h: HS.mem) (x: t { invariant h x }) =
  B.as_seq h (snd x)

let loc (x: t) = B.loc_buffer (snd x)

/// Interestingly enough, there is no need to define a low-level version of
/// ``add_carry``: it is already valid Low* code, since it deals with machine
/// integers. Pairs might introduce a runtime inefficiency but we'll see how to
/// limit that.

/// I was writing the body of add', then realized that the two symmetrical cases
/// could be hoisted into a separate function. It's always better to factor
/// code, and separate functions allow for more robust proofs. Sharing
/// preconditions is also great!
let add'_pre (dst x y: t) (c0: U32.t) (h0: HS.mem) =
  invariant h0 dst /\ invariant h0 x /\ invariant h0 y /\
  B.loc_disjoint (loc dst) (loc x) /\
  B.loc_disjoint (loc dst) (loc y) /\
  // Note here that I am doing the ``+1`` with a nat rather than a U32,
  // otherwise I would have to add a precondition related to the fact that
  // neither x or y can have an array size of max_length. I'll add this
  // precondition at the very end of this module.
  U32.v (fst dst) == U32.v (max32 (fst x) (fst y)) + 1 /\
  Spec.v (as_seq h0 dst) == 0

let add'_post (dst x y: t) (c0: U32.t) (h0: HS.mem) () (h1: HS.mem) =
  B.modifies (loc dst) h0 h1 /\
  invariant h0 dst /\ invariant h0 x /\ invariant h0 y /\
  // Do not use `==` with sequences! It doesn't trigger automatically and
  // patterns cannot be written over ==, meaning that you don't get the
  // benefits of SMTPat triggers for reasoning about your sequences.
  as_seq h1 dst `S.equal` Spec.add' (as_seq h0 x) (as_seq h0 y) c0

/// I really want to separate this function but it needs recursion, so I just do
/// an open recursion and rely on inline_for_extraction to get the code I want.
/// Note that in Low*, type abbreviations that are used to annotate functions
/// later on MUST BE inline for extraction (they're used to understand how many
/// arguments there are to the function).
inline_for_extraction noextract
let add'_t = dst:t -> x:t -> y:t -> c0:U32.t -> Stack unit
  (requires add'_pre dst x y c0)
  (ensures add'_post dst x y c0)

/// So let's focus on the simple case first where one of the two sequences is zero.
inline_for_extraction noextract
val add'_zero (add': add'_t) (dst x y: t) (c0: U32.t): Stack unit
  (requires fun h0 -> fst x = 0ul /\ fst y <> 0ul /\ add'_pre dst x y c0 h0)
  (ensures add'_post dst x y c0)

#push-options "--z3rlimit 30"
inline_for_extraction noextract
let add'_zero add' dst x y c0 =
  let x_l, x_b = x in
  let y_l, y_b = y in
  let dst_l, dst_b = dst in

  // I added this bit afterwards, so I'm using lexicographic number for my h variables.
  (**) let h00 = ST.get () in
  // Ninja trick. Remember how I was previously preaching for a zero-fuel
  // zero-ifuel approach to proofs. Here, we need to unroll the definition of
  // add' in order to prove that we are doing the right thing and generating the
  // right recursive call. This would normally warrant a --fuel 1 setting.
  // However, we can manually instruct the normalizer to perform a step of
  // reduction on the desired post-condition for this function, revealing its
  // definition in the process, and skipping the need for fuel altogether since
  // this is performed in F* without any reliance on Z3.
  (**) norm_spec [zeta; iota; primops; delta_only [`%Spec.add']]
    (Spec.add' (B.as_seq h00 x_b) (B.as_seq h00 y_b) c0);

  // Split y. In my experience, if you are doing modifications to two different
  // sub-parts of a buffer, then make sure you materialize these disjoint parts
  // by calling ``sub`` twice. This ensures that the equational lemmas for the
  // modifies theory trigger, hence giving you "for free" the fact that
  // modifying one half of the buffer leaves the other one unchanged. Without
  // that, you'd have to do manual sequence reasoning by hand which would be
  // very painful.
  let y_hd = B.sub y_b 0ul 1ul in
  let y_tl_l = y_l `U32.sub` 1ul in
  let y_tl = B.sub y_b 1ul y_tl_l in

  // Split dst.
  let dst_hd = B.sub dst_b 0ul 1ul in
  let dst_tl_l = dst_l `U32.sub` 1ul in
  let dst_tl = B.sub dst_b 1ul dst_tl_l in

  (**) let h0 = ST.get () in
  (**) v_zero_tail (B.as_seq h0 dst_b);

  // Actual computation. Note that this will *not* generate a pair in the
  // resulting C code! With the inline_for_extraction on Spec.add_carry, this
  // becomes (in the internal KreMLin AST) something like:
  //   match (let a = ... in let c = ... in a, c) with (a', c')
  // KreMLin hoists the let-bindings:
  //   let a = ... in
  //   let c = ... in
  //   match a, c with a', c' -> ...
  // then gets rid of the match as it is a trivial match on a pair literal. This
  // is a well-known technique that applies to tuples of any lengths, and allows
  // sharing copious amounts of code between spec and implementation. It is used
  // pervasively in HACL*.
  // See https://github.com/FStarLang/kremlin/blob/04054342cb527ecb97633d0d88a739ae0b320146/src/DataTypes.ml#L1014
  let a, c1 = Spec.add_carry y_b.(0ul) c0 in
  dst_hd.(0ul) <- a;

  (**) let h1 = ST.get () in
  add' (dst_tl_l, dst_tl) x (y_tl_l, y_tl) c1;

  (**) let h2 = ST.get () in
  // The proof felt sluggish at this stage (it really should've come back
  // instantly!). Here's what I did: I set fuel to 0 (leaving the proof of
  // correctness aside for the moment), then knowing that I shouldn't need fuel
  // for the rest of the sequence-based reasoning, I added ``admit ()`` right below.
  // I got an error for the recursive call, which led me to write
  // ``v_zero_tail`` and call it manually. The proof was pretty snappy after
  // that.
  assert (B.get h1 dst_hd 0 == B.get h2 dst_hd 0);

  // Trick: this let-binding is the last element in the ;-separated sequence
  // that makes up this function body, so it's ok to use Ghost code from here on
  // since the whole let-binding will enjoy unit-ghost to unit-tot promotion.
  let dst1 = B.as_seq h2 dst_b in

  // Always use S.equal for sequences!
  calc (S.equal) {
    dst1;
  (S.equal) { lemma_slice dst1 1 }
    S.slice dst1 0 1 `S.append` S.slice dst1 1 (S.length dst1);
  (S.equal) { }
    S.cons a (B.as_seq h2 dst_tl);
  (S.equal) { }
    S.cons a (Spec.add' (B.as_seq h1 x_b) (B.as_seq h1 y_tl) c1);
  (S.equal) { lemma_empty (B.as_seq h1 x_b) }
    S.cons a (Spec.add' S.empty (B.as_seq h1 y_tl) c1);
  (S.equal) { }
    S.cons a (Spec.add' S.empty (B.as_seq h0 y_tl) c1);
  (S.equal) { S.lemma_tl (B.get h0 y_b 0) (B.as_seq h0 y_tl) }
    // Frankly, at this stage, it appears that using S.tail in the spec was a
    // mistake. So much more work!
    S.cons a (Spec.add' S.empty (S.tail (B.as_seq h0 y_b)) c1);
  }
#pop-options


/// For stateful functions where the types tend to be massive, I always separate
/// the val from the let. Allows type-checking both separately, and making sure
/// the type even checks.
val add': add'_t

/// Of course, a fuel setting of 1 would work as an alternative to the normalization trick demonstrated earlier.
#push-options "--z3rlimit 50 --fuel 1"
let rec add' dst x y c0 =
  let x_l, x_b = x in
  let y_l, y_b = y in
  let dst_l, dst_b = dst in

  if x_l = 0ul && y_l = 0ul then
    dst_b.(0ul) <- c0

  else if x_l = 0ul then
    add'_zero add' dst x y c0

  else if y_l = 0ul then
    add'_zero add' dst y x c0

  else
    let x_hd = B.sub x_b 0ul 1ul in
    let x_tl_l = x_l `U32.sub` 1ul in
    let x_tl = B.sub x_b 1ul x_tl_l in

    let y_hd = B.sub y_b 0ul 1ul in
    let y_tl_l = y_l `U32.sub` 1ul in
    let y_tl = B.sub y_b 1ul y_tl_l in

    let dst_hd = B.sub dst_b 0ul 1ul in
    let dst_tl_l = dst_l `U32.sub` 1ul in
    let dst_tl = B.sub dst_b 1ul dst_tl_l in

    (**) let h0 = ST.get () in
    (**) v_zero_tail (B.as_seq h0 dst_b);
    // I've had in the past typing errors when arguments to the function are
    // effectful computations. If that happens, just let-bind the arguments.
    let a1, c1 = Spec.add_carry x_hd.(0ul) y_hd.(0ul) in
    let a2, c2 = Spec.add_carry a1 c0 in
    dst_hd.(0ul) <- a2;


    (**) let h1 = ST.get () in
    // I tend to structure my code with `let h... = ST.get ()` before every
    // stateful operation, since proofs almost always need to refer to every
    // single point of the state. The (**) is a nice trick that indicates which
    // lines are for the purposes of proofs only. The fstar-mode.el supports
    // hiding those.
    let c = U32.(c1 +^ c2) in
    // Why am I calling this lemma? Well. I noticed that the proof was not as
    // snappy as it should be. Using the "sliding admit" technique, I moved an
    // admit up and down the function to figure out where the time was spent. I
    // realized that once more the time was spent in the recursive call.
    // However, I already was calling ``v_zero_tail`` manually, so it had to be
    // something else. So right before the recursive call, I started asserting
    // parts of the precondition one by one, to figure out which was was the
    // culprit. It turns out that the ``max`` condition was adding quite a few
    // seconds to the proof! In a sense, it's not surprising, because it's
    // non-linear arithmetic, and while it always works great on small examples,
    // it a larger context, it can easily send the proof off the rails. So I
    // just moved that fact to a separate lemma, called it manually, and the
    // proof became very fast again.
    max_fact dst_l x_l y_l;
    add' (dst_tl_l, dst_tl) (x_tl_l, x_tl) (y_tl_l, y_tl) c;

    (**) let h2 = ST.get () in
    (**) let dst1 = B.as_seq h2 dst_b in

    // This is mostly a copy-paste of the previous calc statement. As mentioned
    // above, I much prefer littering my code with calc's rather than dropping
    // the two manual lemma calls that are needed because the proof is fresh in
    // my head. At this stage, the proof takes a few seconds; rlimit 50 is
    // commendable (it's still pretty low) and the function body is relatively
    // big, so perhaps it's not that surprising that the function should take a
    // few seconds to go through. At this stage, I'm mildly confident that the
    // proof is robust enough thanks to the calc statement, so I'm moving on,
    // but a more thorough investigation would be in order to understand why
    // this proof sometimes takes a while.
    calc (S.equal) {
      dst1;
    (S.equal) { lemma_slice dst1 1 }
      S.slice dst1 0 1 `S.append` S.slice dst1 1 (S.length dst1);
    (S.equal) { slice_create 0 dst1 }
      S.cons a2 (S.slice dst1 1 (S.length dst1));
    (S.equal) { }
      S.cons a2 (B.as_seq h2 dst_tl);
    (S.equal) { }
      S.cons a2 (Spec.add' (B.as_seq h1 x_tl) (B.as_seq h1 y_tl) c);
    (S.equal) { }
      S.cons a2 (Spec.add' (B.as_seq h0 x_tl) (B.as_seq h0 y_tl) c);
    (S.equal) { S.lemma_tl (B.get h0 y_b 0) (B.as_seq h0 y_tl) }
      S.cons a2 (Spec.add' (B.as_seq h0 x_tl) (S.tail (B.as_seq h0 y_b)) c);
    (S.equal) { S.lemma_tl (B.get h0 x_b 0) (B.as_seq h0 x_tl) }
      S.cons a2 (Spec.add' (S.tail (B.as_seq h0 x_b)) (S.tail (B.as_seq h0 y_b)) c);
    }

#pop-options

/// We now demonstrate a function that performs an allocation and returns the
/// corresponding value. This showcases heap-based allocation. Note that we are
/// no longer in the Stack effect (which means "only stack allocations"); ST
/// allows heap allocations.
val add_alloc (r: HS.rid) (x y: t): ST t
  (requires fun h0 ->
    invariant h0 x /\ invariant h0 y /\
    U32.v (fst x) <> UInt.max_int 32 /\
    U32.v (fst y) <> UInt.max_int 32 /\
    ST.is_eternal_region r)
  (ensures fun h0 z h1 ->
    invariant h1 x /\ invariant h1 y /\ invariant h1 z /\
    // There are many key things to reveal to clients when returning a fresh
    // allocation. Lacking these, a client will not be able to reason about the
    // return value.
    //
    // 1. No existing memory locations were modified. (Allocating does not count
    // towards the modifies clause).
    B.(modifies loc_none h0 h1) /\
    // 2. The new location is fresh. Thanks various lemmas and patterns, clients
    // will be able to deduce disjointness from any allocation that they knew
    // existed before.
    B.(fresh_loc (loc_buffer (snd z)) h0 h1) /\
    // 3. Unless a region is provided, this function will never be useful to
    // verified clients. So, we need to say that we allocated the function in
    // the requested region.
    B.(loc_includes (loc_region_only true r) (loc_buffer (snd z))))

#push-options "--z3rlimit 100"
let add_alloc r x y =
  // Without these bindings, some SMT patterns don't trigger on x_l and prevent
  // me from concluding liveness of x_l after malloc. Perhaps it would've been
  // wiser to avoid pairs and pass arguments separately?
  let x_l, x_b = x in
  let y_l, y_b = y in

  let h0 = ST.get () in
  let dst_l = max32 (fst x) (fst y) `U32.add` 1ul in
  let dst_b = B.malloc r 0ul dst_l in
  let dst = dst_l, dst_b in

  let h1 = ST.get () in
  v_all_zeroes (B.as_seq h1 dst_b);
  add' (dst_l, dst_b) x y 0ul;

  let h2 = ST.get () in
  // A key lemma is needed here. Since the library is a bit big, I usually just
  // skim EverCrypt.Hash.Incremental which I authored a while ago and contains
  // similar heap-manipulating functions.
  B.(modifies_only_not_unused_in loc_none h0 h2);
  dst

/// At this stage, a nice exercise would be to write an alternative
/// specification using Spec.Loops. Then perform a proof of spec equivalence
/// between add'_loop and add'. Finally, write a Low* implementation of
/// add'_loop and show that it performs an addition using the spec equivalence
/// lemma.
///
/// Another nice exercise would be to use Impl.Bignum.Intrinsics instead of Spec.add_carry.
