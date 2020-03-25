/// Main specification
/// ==================

module Spec.Bignum

/// This specification module provides a functional implementation of bignum
/// addition. Think of it as a intermediate spec: it is more concrete than the
/// top-level spec (which is, simply, ``Prims.op_Multiplication``), but it is
/// functional, in the sense that it does not manipulate any implementation
/// details (i.e. this code is not Low*) and only extracts to OCaml.

/// The preferred style is to open as few modules as possible; this prevents
/// future breakages, as new names may appear in a module at any given time,
/// resulting in unpredictable shadowings; it also facilitates reading the code
/// on GitHub without an interactive mode.

/// Another note: it's good to keep specifications executable (i.e. in Pure);
/// specifications in GTot complicate things as they incur coercions; also, this
/// makes the specs non-executable, which just makes debugging harder.

module S = FStar.Seq

/// People usually enjoy short abbreviations like these, as they work with the
/// local open syntax (à la OCaml). It's always possible to use ``UInt32`` (as
/// the ``FStar`` namespace is always open), but this doesn't work with the
/// (local) open syntax.
module U32 = FStar.UInt32
module U64 = FStar.UInt64

/// These are nice abbreviations but we don't want them to pollute the generated
/// OCaml code, so we use the two keywords to make sure they end up being just
/// aliases.
inline_for_extraction noextract
let u64_of_u32 = FStar.Int.Cast.Full.uint32_to_uint64
inline_for_extraction noextract
let u32_of_u64 = FStar.Int.Cast.Full.uint64_to_uint32

/// Back in ancient times, the ``*`` operator served both as a tuple operator
/// and as a multiplication. Now the preferred way to write a tuple is with the
/// ``&`` operator, leaving ``*`` for multiplication only. For
/// backwards-compatibility, this was not made the default, so we open this
/// module to ensure ``*`` is multiplication over natural numbers.
open FStar.Mul

/// The preferred style is to work with zero fuel (never unroll recursive
/// functions in SMT) and zero ifuel (never perform inversion automatically in
/// SMT). This makes proofs more robust, more predictible, faster, and ensures
/// that non-zero values are expected and documented. Via the push-pop options
/// syntax, this can be made a local change.
#set-options "--fuel 0 --ifuel 0"

/// There exists a module called ``FStar.Integers`` that offers overloaded
/// operators for machine integers, but it has its own pitfalls, and I don't
/// recommend using it until https://github.com/FStarLang/FStar/issues/1691 is
/// fixed. In the meanwhile, let's use ugly operators with suffixes.

/// Our type for the functional implementation of bignums is a sequence of words
/// (also known as limbs in this context). This will be a little-endian
/// representation, where the least significant word comes at index 0 in the
/// sequence. We choose sequence over list as low-level arrays are reflected in
/// a given heap as a sequence -- this will thus make the proof of refinement
/// (the Low* implementation matches the spec) easier to perform.
let t = S.seq UInt32.t

let max = pow2 32

/// Most modules define a ``v`` function that maps a type to its "value", or
/// "representation", i.e. the reflection of a ``t`` as a high-level value.
let rec v (x: t): Tot nat (decreases (S.length x)) =
  // Note that we use decidable equality here since we intend to extract this
  // code to OCaml.
  if S.length x = 0 then
    0
  else
    U32.v (S.head x) + max * v (S.tail x)

/// A stylistic note: parentheses are oftentimes ommitted after ``requires``and
/// ``ensures`` but for some reason are still needed for ``decreases``. See
/// https://github.com/FStarLang/FStar/issues/1765
inline_for_extraction
let add_carry (x y: U32.t): Pure (U32.t & U32.t)
  (requires True)
  (ensures fun z ->
    let open U32 in
    let a, c = z in
    U32.v x + U32.v y == U32.v a + pow2 32 * U32.v c /\
    U32.v c <= 1
  )
=
  let a = U32.(x +%^ y) in
  assert (U32.v a == (U32.v x + U32.v y) % pow2 32);

  let x64 = u64_of_u32 x in
  let y64 = u64_of_u32 y in
  let c = u32_of_u64 U64.((x64 +^ y64) >>^ 32ul) in
  // This is a precondition of the modulo_modulo_lemma. Z3 stands no chance of
  // solving this, so I just preemptively bring this fact into the context by
  // using F*'s reduction capabilities (implemented under the hood using
  // efficient bignum arithmetic via Zarith).
  assert_norm (pow2 64 = pow2 32 * pow2 32);
  // Nonmodular arithmetic proofs do not generally go through with Z3. If they
  // do, it's a piece of luck, and you should not rely on it! So, instead, I use
  // a calc statement to make the proof explicit, help with the reasoning, and
  // make sure whoever needs to maintain this proof in the future has a base to
  // work with.
  calc (==) {
    U32.v c;
  (==) { }
    U64.(v ((x64 +^ y64) >>^ 32ul)) % pow2 64 % pow2 32;
  (==) { FStar.Math.Lemmas.modulo_modulo_lemma U64.(v ((x64 +^ y64) >>^ 32ul)) (pow2 32) (pow2 32) }
    U64.(v ((x64 +^ y64) >>^ 32ul)) % pow2 32;
  (==) { FStar.UInt.shift_right_value_lemma #64 U64.(v (x64 +^ y64)) 32 }
    (U64.(v (x64 +^ y64)) / pow2 32) % pow2 32;
  (==) { }
    ((U32.v x + U32.v y) / pow2 32) % pow2 32;
  };

  // Precondition of small_modulo_lemma_1. The naming of lemmas in
  // FStar.Math.Lemmas is really suboptimal -- any help most welcome, of course.
  assert_norm ((UInt.max_int 32 + UInt.max_int 32) / pow2 32 < pow2 32);

  // These proofs are tedious; they are, however, robust, since each step of a
  // calc statement is proven in isolation. Always use calc when you can!
  // Nonlinear arithmetic is generally highly unreliable with Z3, and very
  // manual proofs are oftentimes the best way to go. Some people even choose to
  // disable non-linear arithmetic altogether.
  calc (==) {
    U32.v a + max * U32.v c;
  (==) {}
    (U32.v x + U32.v y) % pow2 32 + max * (((U32.v x + U32.v y) / pow2 32) % pow2 32);
  (==) {}
    (U32.v x + U32.v y) % pow2 32 + (((U32.v x + U32.v y) / pow2 32) % pow2 32) * pow2 32;
  (==) { FStar.Math.Lemmas.small_modulo_lemma_1 ((U32.v x + U32.v y) / pow2 32) (pow2 32) }
    (U32.v x + U32.v y) % pow2 32 + (((U32.v x + U32.v y) / pow2 32)) * pow2 32;
  (==) { FStar.Math.Lemmas.euclidean_division_definition (U32.v x + U32.v y) (pow2 32) }
    U32.v x + U32.v y;
  };
  a, c

/// Here, we need to unroll the definition of add at least once with the SMT.
/// With push/pop, the change is only local to this function.
#push-options "--fuel 1"
let v_0 (x: t): Lemma
  (requires S.length x = 0)
  (ensures v x = 0)
  [ SMTPat (v x) ]
=
  ()
#pop-options

/// I personally prefer --fuel because it combines max_fuel and initial_fuel,
/// meaning that you really mean to say that your proof requires 2 units of
/// fuel. These two lemmas with patterns mean that Z3 will automatically unfold
/// v but, assuming fuel is zero, will not attempt to unfold anything
/// else. There is a more systematic way of achieving this with opaque / reveal,
/// but see the advanced topic for that.
#push-options "--fuel 2"
let v_1 (x: U32.t) (y: t): Lemma
  (ensures v (S.cons x y) == U32.v x + pow2 32 * (v y))
  [ SMTPat (v (S.cons x y)) ]
=
  S.lemma_tl x y
#pop-options

/// Since I authored the two lemmas above, I don't need to rely on Z3 unfolding
/// the definition of ``v`` for my proof to go through. This is in line with my
/// earlier digression about always running with zero fuel and ifuel.
///
/// I thought about requiring ``S.length x = S.length y`` and then having a
/// helper function that removes this precondition. I thought it'd be easier to
/// implement later if I wrote a functional implementation capable of dealing
/// with any lengths for x and y. I also thought that it would be a tedious
/// proof to do in the helper too, so might as well do it once. I guess it's a
/// matter of taste and personal preference at this stage.
///
/// This function failed once as I was trying to process it in the interactive
/// mode, then succeeded again on the second try without me changing anything.
/// This generally means one of two things: either the proof is operating very
/// close to the maximum allowed rlimit, or the proof is very unstable and I
/// should make it more robust. I used the ``quake`` option which tweaks the
/// z3seed to ensure that the proof is reasonably robust. It probably was an
/// rlimit issue (after all, I had not tweaked the default rlimit setting until
/// now!).
#push-options "--z3rlimit 20" // --quake 3
let rec add' (x y: t) (c0: U32.t): Pure t
  (requires True)
  (ensures fun z -> v x + v y + U32.v c0 = v z)
  (decreases (S.length x + S.length y))
=
  if S.length x = 0 && S.length y = 0 then
    S.cons c0 S.empty
  else if S.length x = 0 then
    let y_head = S.head y in
    let y_tail = S.tail y in
    let a, c1 = add_carry y_head c0 in
    let r = S.cons a (add' S.empty y_tail c1) in
    // Oftentimes, when I don't have any idea why the proof doesn't go through, I use a calc statement and write the steps in order.
    calc (==) {
      v r;
      // Here I realized I needed to reason about the value of v (cons x y).
      // While I could augment the fuel to allow Z3 to unroll the definition of
      // v and prove the property as-needed, I chose to make it a separate
      // lemma, which was helpful because I realized that even the separate
      // lemma needed S.lemma_tl.
    (==) { }
      U32.v a + pow2 32 * v (add' S.empty y_tail c1);
    (==) { }
      U32.v a + pow2 32 * (v y_tail + U32.v c1);
      // Here I realized that I needed non-linearity. A manual lemma invocation
      // is always preferred. Stay tuned for a better way of doing this below.
    (==) { FStar.Math.Lemmas.distributivity_add_right (pow2 32) (v y_tail) (U32.v c1) }
      U32.v a + pow2 32 * v y_tail + pow2 32 * U32.v c1;
    (==) { }
      U32.v y_head + U32.v c0 + pow2 32 * v y_tail;
      // It's unfortunate that we have to call this lemma by hand. But adding a
      // pattern to it might break a lot of other proofs!
    (==) { S.lemma_tl y_head y_tail }
      v y + U32.v c0;
    };
    r
  else if S.length y = 0 then
    let x_head = S.head x in
    let x_tail = S.tail x in
    let a, c1 = add_carry x_head c0 in
    let r = S.cons a (add' S.empty x_tail c1) in
    // Since this case is identical to the one above, I could just take the two
    // relevant lemma invocations and the proof would still go through without a
    // calc statement. I prefer keeping the calc for proof robustness.
    calc (==) {
      v r;
    (==) { }
      U32.v a + pow2 32 * v (add' S.empty x_tail c1);
    (==) { }
      U32.v a + pow2 32 * (v x_tail + U32.v c1);
    (==) { FStar.Math.Lemmas.distributivity_add_right (pow2 32) (v x_tail) (U32.v c1) }
      U32.v a + pow2 32 * v x_tail + pow2 32 * U32.v c1;
    (==) { }
      U32.v x_head + U32.v c0 + pow2 32 * v x_tail;
    (==) { S.lemma_tl x_head x_tail }
      v x + U32.v c0;
    };
    r
  else
    let x_head = S.head x in
    let x_tail = S.tail x in
    S.lemma_tl x_head x_tail;
    let y_head = S.head y in
    let y_tail = S.tail y in
    S.lemma_tl y_head y_tail;
    let a1, c1 = add_carry x_head y_head in
    let a2, c2 = add_carry a1 c0 in
    let c = U32.(c1 +^ c2) in
    let r = S.cons a2 (add' x_tail y_tail c) in
    // As usual, a calc statement is more robust.
    calc (==) {
      v r;
    (==) { }
      U32.v a2 + pow2 32 * v (add' x_tail y_tail c);
    (==) { }
      U32.v a2 + pow2 32 * (v x_tail + v y_tail + U32.v c1 + U32.v c2);
    (==) { _ by (FStar.Tactics.CanonCommSemiring.int_semiring ()) }
      // The main reason for using the tactic here is that this is basic
      // distributivity, but I know from experience that Z3 might struggle with
      // this fact, and that I don't want to write all of the arguments to all
      // three calls to the distributivity lemma by hand.
      U32.v a2 + pow2 32 * v x_tail + pow2 32 * v y_tail + pow2 32 * U32.v c1 + pow2 32 * U32.v c2;
    };
    // Knowing from the S.length x = 0 case above that reasoning about S.tail
    // almost always requires a call to S.lemma_tl, I pre-emptively called it
    // for both x and y above. (Doesn't hurt.) With that, the rest of the proof
    // goes through automatically.
    r
#pop-options

/// No particular reason here for using Tot over Pure. Maybe because it's more compact?
let add (x y: t): Tot (z:t { v z = v x + v y }) =
  add' x y 0ul

/// The next steps are of course to define ``mul_carry``, ``mul'`` and ``mul``.
/// Another cool next step would be to make this module parametric over the limb
/// type, to allow, say, U32 or U64.
