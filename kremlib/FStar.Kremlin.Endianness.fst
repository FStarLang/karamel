module FStar.Kremlin.Endianness

open FStar.Mul
open FStar.HyperStack.All

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S = FStar.Seq

(* Selectively imported from Hacl*'s FStar.Endianness.fst library, with several
name changes *)

type bytes = S.seq U8.t

/// lt_to_n interprets a byte sequence as a little-endian natural number
val le_to_n : b:bytes -> Tot nat (decreases (S.length b))
let rec le_to_n b =
  if S.length b = 0 then 0
  else U8.v (S.head b) + pow2 8 * le_to_n (S.tail b)

/// be_to_n interprets a byte sequence as a big-endian natural number
val be_to_n : b:bytes -> Tot nat (decreases (S.length b))
let rec be_to_n b =
  if S.length b = 0 then 0
  else U8.v (S.last b) + pow2 8 * be_to_n (S.slice b 0 (S.length b - 1))

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
  Tot (b:bytes{S.length b == U32.v len /\ n == le_to_n b})
  (decreases (U32.v len))
let rec n_to_le len n =
  if len = 0ul then
    S.empty
  else
    let len = U32.(len -^ 1ul) in
    let byte = U8.uint_to_t (n % 256) in
    let n' = n / 256 in
    Math.pow2_plus 8 (8 * U32.v len);
    assert(n' < pow2 (8 * U32.v len ));
    let b' = n_to_le len n' in
    let b = S.cons byte b' in
    S.lemma_eq_intro b' (S.tail b);
    b

/// n_to_be encodes a numbers as a big-endian byte sequence of a fixed,
/// sufficiently large length
val n_to_be:
  len:U32.t -> n:nat{n < pow2 (8 * U32.v len)} ->
  Tot (b:bytes{S.length b == U32.v len /\ n == be_to_n b})
  (decreases (U32.v len))
let rec n_to_be len n =
  if len = 0ul then
    S.empty
  else
    let len = U32.(len -^ 1ul) in
    let byte = U8.uint_to_t (n % 256) in
    let n' = n / 256 in
    Math.pow2_plus 8 (8 * U32.v len);
    assert(n' < pow2 (8 * U32.v len ));
    let b' = n_to_be len n' in
    let b'' = S.create 1 byte in
    let b = S.append b' b'' in
    S.lemma_eq_intro b' (S.slice b 0 (U32.v len));
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

(** A series of specializations to deal with machine integers *)

let uint32_of_le (b: bytes { S.length b = 4 }) =
  let n = le_to_n b in
  lemma_le_to_n_is_bounded b;
  UInt32.uint_to_t n

let le_of_uint32 (x: UInt32.t): b:bytes{ S.length b = 4 } =
  n_to_le 4ul (UInt32.v x)

let uint32_of_be (b: bytes { S.length b = 4 }) =
  let n = be_to_n b in
  lemma_be_to_n_is_bounded b;
  UInt32.uint_to_t n

let be_of_uint32 (x: UInt32.t): b:bytes{ S.length b = 4 } =
  n_to_be 4ul (UInt32.v x)

let uint64_of_le (b: bytes { S.length b = 8 }) =
  let n = le_to_n b in
  lemma_le_to_n_is_bounded b;
  UInt64.uint_to_t n

let le_of_uint64 (x: UInt64.t): b:bytes{ S.length b = 8 } =
  n_to_le 8ul (UInt64.v x)

let uint64_of_be (b: bytes { S.length b = 8 }) =
  let n = be_to_n b in
  lemma_be_to_n_is_bounded b;
  UInt64.uint_to_t n

let be_of_uint64 (x: UInt64.t): b:bytes{ S.length b = 8 } =
  n_to_be 8ul (UInt64.v x)

let rec seq_uint32_of_le (l: nat) (b: bytes{ S.length b = 4 * l }):
  s:S.seq UInt32.t { S.length s = l }
=
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 4 in
    S.cons (uint32_of_le hd) (seq_uint32_of_le (l - 1) tl)

let rec le_of_seq_uint32 (s: S.seq UInt32.t):
  Tot (b:bytes { S.length b = 4 * S.length s })
    (decreases (S.length s))
=
  if S.length s = 0 then
    S.empty
  else
    S.append (le_of_uint32 (S.head s)) (le_of_seq_uint32 (S.tail s))

let rec seq_uint32_of_be (l: nat) (b: bytes{ S.length b = 4 * l }):
  s:S.seq UInt32.t { S.length s = l }
=
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 4 in
    S.cons (uint32_of_be hd) (seq_uint32_of_be (l - 1) tl)

let rec be_of_seq_uint32 (s: S.seq UInt32.t):
  Tot (b:bytes { S.length b = 4 * S.length s })
    (decreases (S.length s))
=
  if S.length s = 0 then
    S.empty
  else
    S.append (be_of_uint32 (S.head s)) (be_of_seq_uint32 (S.tail s))

let rec seq_uint64_of_le (l: nat) (b: bytes{ S.length b = 8 * l }):
  s:S.seq UInt64.t { S.length s = l }
=
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 8 in
    S.cons (uint64_of_le hd) (seq_uint64_of_le (l - 1) tl)

let rec le_of_seq_uint64 (s: S.seq UInt64.t):
  Tot (b:bytes { S.length b = 8 * S.length s })
    (decreases (S.length s))
=
  if S.length s = 0 then
    S.empty
  else
    S.append (le_of_uint64 (S.head s)) (le_of_seq_uint64 (S.tail s))

let rec seq_uint64_of_be (l: nat) (b: bytes{ S.length b = 8 * l }):
  s:S.seq UInt64.t { S.length s = l }
=
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 8 in
    S.cons (uint64_of_be hd) (seq_uint64_of_be (l - 1) tl)

let rec be_of_seq_uint64 (s: S.seq UInt64.t):
  Tot (b:bytes { S.length b = 8 * S.length s })
    (decreases (S.length s))
=
  if S.length s = 0 then
    S.empty
  else
    S.append (be_of_uint64 (S.head s)) (be_of_seq_uint64 (S.tail s))


#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 50"

let rec offset_uint32_be (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 4 * n /\
      i < n))
    (ensures (
      S.index (seq_uint32_of_be n b) i == uint32_of_be (S.slice b (4 * i) (4 * i + 4))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint32_of_be n b) i) ]
=
  if S.length b = 0 then
    false_elim ()
  else
    let hd, tl = Seq.split b 4 in
    if i = 0 then
      ()
    else
      offset_uint32_be tl (n - 1) (i - 1)

let rec offset_uint32_le (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 4 * n /\
      i < n))
    (ensures (
      S.index (seq_uint32_of_le n b) i == uint32_of_le (S.slice b (4 * i) (4 * i + 4))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint32_of_le n b) i) ]
=
  if S.length b = 0 then
    false_elim ()
  else
    let hd, tl = Seq.split b 4 in
    if i = 0 then
      ()
    else
      offset_uint32_le tl (n - 1) (i - 1)

let rec offset_uint64_be (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 8 * n /\
      i < n))
    (ensures (
      S.index (seq_uint64_of_be n b) i == uint64_of_be (S.slice b (8 * i) (8 * i + 8))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint64_of_be n b) i) ]
=
  if S.length b = 0 then
    false_elim ()
  else
    let hd, tl = Seq.split b 8 in
    if i = 0 then
      ()
    else
      offset_uint64_be tl (n - 1) (i - 1)

let rec offset_uint64_le (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 8 * n /\
      i < n))
    (ensures (
      S.index (seq_uint64_of_le n b) i == uint64_of_le (S.slice b (8 * i) (8 * i + 8))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint64_of_le n b) i) ]
=
  if S.length b = 0 then
    false_elim ()
  else
    let hd, tl = Seq.split b 8 in
    if i = 0 then
      ()
    else
      offset_uint64_le tl (n - 1) (i - 1)
