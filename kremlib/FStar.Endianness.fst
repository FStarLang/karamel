module FStar.Endianness

open FStar.Seq
open FStar.Mul
open FStar.HyperStack.All

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas

(* Selectively imported from Hacl*'s FStar.Endianness.fst library, with several
name changes *)

type bytes = seq U8.t

/// lt_to_n interprets a byte sequence as a little-endian natural number
val le_to_n : b:bytes -> Tot nat (decreases (length b))
let rec le_to_n b =
  if Seq.length b = 0 then 0
  else U8.v (head b) + pow2 8 * le_to_n (tail b)

/// be_to_n interprets a byte sequence as a big-endian natural number
val be_to_n : b:bytes -> Tot nat (decreases (length b))
let rec be_to_n b =
  if Seq.length b = 0 then 0
  else U8.v (last b) + pow2 8 * be_to_n (slice b 0 (length b - 1))

private val lemma_euclidean_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidean_division r b q = ()

private val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b == a * (b + 1))
let lemma_factorise a b = ()

val lemma_le_to_n_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (le_to_n b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))
let rec lemma_le_to_n_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 1 (Seq.length b) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_le_to_n_is_bounded s;
    assert(UInt8.v (Seq.index b 0) < pow2 8);
    assert(le_to_n s < pow2 (8 * Seq.length s));
    assert(le_to_n b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (UInt8.v (Seq.index b 0)) (le_to_n s) (pow2 8);
    assert(le_to_n b <= pow2 8 * (le_to_n s + 1));
    assert(le_to_n b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end

val lemma_be_to_n_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (be_to_n b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))
let rec lemma_be_to_n_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 0 (Seq.length b - 1) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_be_to_n_is_bounded s;
    assert(UInt8.v (Seq.last b) < pow2 8);
    assert(be_to_n s < pow2 (8 * Seq.length s));
    assert(be_to_n b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (UInt8.v (Seq.last b)) (be_to_n s) (pow2 8);
    assert(be_to_n b <= pow2 8 * (be_to_n s + 1));
    assert(be_to_n b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end

/// n_to_le encodes a number as a little-endian byte sequence of a fixed,
/// sufficiently large length
val n_to_le : len:U32.t -> n:nat{n < pow2 (8 * U32.v len)} ->
  Tot (b:bytes{length b == U32.v len /\ n == le_to_n b})
  (decreases (U32.v len))
let rec n_to_le len n =
  if len = 0ul then
    createEmpty
  else
    let len = U32.(len -^ 1ul) in
    let byte = U8.uint_to_t (n % 256) in
    let n' = n / 256 in
    Math.pow2_plus 8 (8 * U32.v len);
    assert(n' < pow2 (8 * U32.v len ));
    let b' = n_to_le len n' in
    let b = cons byte b' in
    lemma_eq_intro b' (tail b);
    b

/// n_to_be encodes a numbers as a big-endian byte sequence of a fixed,
/// sufficiently large length
val n_to_be:
  len:U32.t -> n:nat{n < pow2 (8 * U32.v len)} ->
  Tot (b:bytes{length b == U32.v len /\ n == be_to_n b})
  (decreases (U32.v len))
let rec n_to_be len n =
  if len = 0ul then
    createEmpty
  else
    let len = U32.(len -^ 1ul) in
    let byte = U8.uint_to_t (n % 256) in
    let n' = n / 256 in
    Math.pow2_plus 8 (8 * U32.v len);
    assert(n' < pow2 (8 * U32.v len ));
    let b' = n_to_be len n' in
    let b'' = create 1 byte in
    let b = append b' b'' in
    lemma_eq_intro b' (slice b 0 (U32.v len));
    b

let n_to_le_inj (len:U32.t) (n1 n2: (n:nat{n < pow2 (8 * U32.v len)})) :
  Lemma (requires (n_to_le len n1 == n_to_le len n2))
        (ensures (n1 == n2)) =
  // this lemma easily follows from le_to_n . (n_to_le len) == id, the inversion
  // proof in the spec for n_to_le
  ()

let n_to_be_inj (len:U32.t) (n1 n2: (n:nat{n < pow2 (8 * U32.v len)})) :
  Lemma (requires (n_to_be len n1 == n_to_be len n2))
        (ensures (n1 == n2)) =
  ()
