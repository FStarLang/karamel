module FStar.Krml.Endianness

open FStar.Mul
open FStar.HyperStack.All

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S = FStar.Seq

(* Selectively imported from Hacl*'s FStar.Endianness.fst library, with several
name changes *)

inline_for_extraction noextract
type bytes = S.seq U8.t

/// lt_to_n interprets a byte sequence as a little-endian natural number
[@(deprecated "FStar.Endianness.le_to_n")]
val le_to_n : b:bytes -> Tot nat (decreases (S.length b))
let rec le_to_n b =
  if S.length b = 0 then 0
  else U8.v (S.head b) + pow2 8 * le_to_n (S.tail b)

/// be_to_n interprets a byte sequence as a big-endian natural number
[@(deprecated "FStar.Endianness.be_to_n")]
val be_to_n : b:bytes -> Tot nat (decreases (S.length b))
let rec be_to_n b =
  if S.length b = 0 then 0
  else U8.v (S.last b) + pow2 8 * be_to_n (S.slice b 0 (S.length b - 1))

[@(deprecated "FStar.Endianness.lemma_euclidean_division")]
private val lemma_euclidean_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidean_division r b q = ()

[@(deprecated "FStar.Endianness.lemma_factorise")]
private val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b == a * (b + 1))
let lemma_factorise a b = ()

[@(deprecated "FStar.Endianness.lemma_le_to_n_is_bounded")]
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

[@(deprecated "FStar.Endianness.lemma_be_to_n_is_bounded")]
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
[@(deprecated "FStar.Endianness.n_to_le")]
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
[@(deprecated "FStar.Endianness.n_to_be")]
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

[@(deprecated "FStar.Endianness.n_to_le_inj")]
let n_to_le_inj (len:U32.t) (n1 n2: (n:nat{n < pow2 (8 * U32.v len)})) :
  Lemma (requires (n_to_le len n1 == n_to_le len n2))
        (ensures (n1 == n2)) =
  // this lemma easily follows from le_to_n . (n_to_le len) == id, the inversion
  // proof in the spec for n_to_le
  ()

[@(deprecated "FStar.Endianness.n_to_be_inj")]
let n_to_be_inj (len:U32.t) (n1 n2: (n:nat{n < pow2 (8 * U32.v len)})) :
  Lemma (requires (n_to_be len n1 == n_to_be len n2))
        (ensures (n1 == n2)) =
  ()

[@(deprecated "FStar.Endianness.be_to_n_inj")]
let rec be_to_n_inj
  (b1 b2: Seq.seq U8.t)
: Lemma
  (requires (Seq.length b1 == Seq.length b2 /\ be_to_n b1 == be_to_n b2))
  (ensures (Seq.equal b1 b2))
  (decreases (Seq.length b1))
= if Seq.length b1 = 0
  then ()
  else begin
    be_to_n_inj (Seq.slice b1 0 (Seq.length b1 - 1)) (Seq.slice b2 0 (Seq.length b2 - 1));
    Seq.lemma_split b1 (Seq.length b1 - 1);
    Seq.lemma_split b2 (Seq.length b2 - 1)
  end

[@(deprecated "FStar.Endianness.le_to_n_inj")]
let rec le_to_n_inj
  (b1 b2: Seq.seq U8.t)
: Lemma
  (requires (Seq.length b1 == Seq.length b2 /\ le_to_n b1 == le_to_n b2))
  (ensures (Seq.equal b1 b2))
  (decreases (Seq.length b1))
= if Seq.length b1 = 0
  then ()
  else begin
    le_to_n_inj (Seq.slice b1 1 (Seq.length b1)) (Seq.slice b2 1 (Seq.length b2));
    Seq.lemma_split b1 1;
    Seq.lemma_split b2 1
  end

[@(deprecated "FStar.Endianness.n_to_be_be_to_n")]
let n_to_be_be_to_n (len: U32.t) (s: Seq.seq U8.t) : Lemma
  (requires (Seq.length s == U32.v len))
  (ensures (
    be_to_n s < pow2 (8 `Prims.op_Multiply` U32.v len) /\
    n_to_be len (be_to_n s) == s
  ))
  [SMTPat (n_to_be len (be_to_n s))]
= lemma_be_to_n_is_bounded s;
  be_to_n_inj s (n_to_be len (be_to_n s))

[@(deprecated "FStar.Endianness.n_to_le_le_to_n")]
let n_to_le_le_to_n (len: U32.t) (s: Seq.seq U8.t) : Lemma
  (requires (Seq.length s == U32.v len))
  (ensures (
    le_to_n s < pow2 (8 `Prims.op_Multiply` U32.v len) /\
    n_to_le len (le_to_n s) == s
  ))
  [SMTPat (n_to_le len (le_to_n s))]
= lemma_le_to_n_is_bounded s;
  le_to_n_inj s (n_to_le len (le_to_n s))

(** A series of specializations to deal with machine integers *)

[@(deprecated "FStar.Endianness.uint32_of_le")]
let uint32_of_le (b: bytes { S.length b = 4 }) =
  let n = le_to_n b in
  lemma_le_to_n_is_bounded b;
  UInt32.uint_to_t n

[@(deprecated "FStar.Endianness.le_of_uint32")]
let le_of_uint32 (x: UInt32.t): b:bytes{ S.length b = 4 } =
  n_to_le 4ul (UInt32.v x)

[@(deprecated "FStar.Endianness.uint32_of_be")]
let uint32_of_be (b: bytes { S.length b = 4 }) =
  let n = be_to_n b in
  lemma_be_to_n_is_bounded b;
  UInt32.uint_to_t n

[@(deprecated "FStar.Endianness.be_of_uint32")]
let be_of_uint32 (x: UInt32.t): b:bytes{ S.length b = 4 } =
  n_to_be 4ul (UInt32.v x)

[@(deprecated "FStar.Endianness.uint64_of_le")]
let uint64_of_le (b: bytes { S.length b = 8 }) =
  let n = le_to_n b in
  lemma_le_to_n_is_bounded b;
  UInt64.uint_to_t n

[@(deprecated "FStar.Endianness.le_of_uint64")]
let le_of_uint64 (x: UInt64.t): b:bytes{ S.length b = 8 } =
  n_to_le 8ul (UInt64.v x)

[@(deprecated "FStar.Endianness.uint64_of_be")]
let uint64_of_be (b: bytes { S.length b = 8 }) =
  let n = be_to_n b in
  lemma_be_to_n_is_bounded b;
  UInt64.uint_to_t n

[@(deprecated "FStar.Endianness.be_of_uint64")]
let be_of_uint64 (x: UInt64.t): b:bytes{ S.length b = 8 } =
  n_to_be 8ul (UInt64.v x)

[@(deprecated "FStar.Endianness.seq_uint32_of_le")]
let rec seq_uint32_of_le (l: nat) (b: bytes{ S.length b = 4 * l }):
  s:S.seq UInt32.t { S.length s = l }
=
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 4 in
    S.cons (uint32_of_le hd) (seq_uint32_of_le (l - 1) tl)

[@(deprecated "FStar.Endianness.le_of_seq_uint32")]
let rec le_of_seq_uint32 (s: S.seq UInt32.t):
  Tot (b:bytes { S.length b = 4 * S.length s })
    (decreases (S.length s))
=
  if S.length s = 0 then
    S.empty
  else
    S.append (le_of_uint32 (S.head s)) (le_of_seq_uint32 (S.tail s))

[@(deprecated "FStar.Endianness.seq_uint32_of_be")]
let rec seq_uint32_of_be (l: nat) (b: bytes{ S.length b = 4 * l }):
  s:S.seq UInt32.t { S.length s = l }
=
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 4 in
    S.cons (uint32_of_be hd) (seq_uint32_of_be (l - 1) tl)

[@(deprecated "FStar.Endianness.be_of_seq_uint32")]
let rec be_of_seq_uint32 (s: S.seq UInt32.t):
  Tot (b:bytes { S.length b = 4 * S.length s })
    (decreases (S.length s))
=
  if S.length s = 0 then
    S.empty
  else
    S.append (be_of_uint32 (S.head s)) (be_of_seq_uint32 (S.tail s))

[@(deprecated "FStar.Endianness.seq_uint64_of_le")]
let rec seq_uint64_of_le (l: nat) (b: bytes{ S.length b = 8 * l }):
  s:S.seq UInt64.t { S.length s = l }
=
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 8 in
    S.cons (uint64_of_le hd) (seq_uint64_of_le (l - 1) tl)

[@(deprecated "FStar.Endianness.le_of_seq_uint64")]
let rec le_of_seq_uint64 (s: S.seq UInt64.t):
  Tot (b:bytes { S.length b = 8 * S.length s })
    (decreases (S.length s))
=
  if S.length s = 0 then
    S.empty
  else
    S.append (le_of_uint64 (S.head s)) (le_of_seq_uint64 (S.tail s))

[@(deprecated "FStar.Endianness.seq_uint64_of_be")]
let rec seq_uint64_of_be (l: nat) (b: bytes{ S.length b = 8 * l }):
  s:S.seq UInt64.t { S.length s = l }
=
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 8 in
    S.cons (uint64_of_be hd) (seq_uint64_of_be (l - 1) tl)

[@(deprecated "FStar.Endianness.be_of_seq_uint64")]
let rec be_of_seq_uint64 (s: S.seq UInt64.t):
  Tot (b:bytes { S.length b = 8 * S.length s })
    (decreases (S.length s))
=
  if S.length s = 0 then
    S.empty
  else
    S.append (be_of_uint64 (S.head s)) (be_of_seq_uint64 (S.tail s))


#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 50"

[@(deprecated "FStar.Endianness.offset_uint32_be")]
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

[@(deprecated "FStar.Endianness.offset_uint32_le")]
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

[@(deprecated "FStar.Endianness.offset_uint64_be")]
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

[@(deprecated "FStar.Endianness.offset_uint64_le")]
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


(** Reasoning about endian-ness and words. *)

#set-options "--max_fuel 1 --z3rlimit 20"

(* TODO: move to FStar.Seq.Properties, with the pattern *)
[@(deprecated "FStar.Endianness.tail_cons")]
let tail_cons (#a: Type) (hd: a) (tl: S.seq a): Lemma
  (ensures (S.equal (S.tail (S.cons hd tl)) tl))
//  [ SMTPat (S.tail (S.cons hd tl)) ]
=
  ()

[@(deprecated "FStar.Endianness.be_of_seq_uint32_append")]
let rec be_of_seq_uint32_append (s1 s2: S.seq U32.t): Lemma
  (ensures (
    S.equal (be_of_seq_uint32 (S.append s1 s2))
      (S.append (be_of_seq_uint32 s1) (be_of_seq_uint32 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (be_of_seq_uint32 s1) (be_of_seq_uint32 s2)) ]
=
  Classical.forall_intro_2 (tail_cons #U32.t); // TODO: this is a local pattern, remove once tail_cons lands in FStar.Seq.Properties
  if S.length s1 = 0 then begin
    assert (S.equal (be_of_seq_uint32 s1) S.empty);
    assert (S.equal (S.append s1 s2) s2);
    ()
  end else begin
    assert (S.equal (S.append s1 s2) (S.cons (S.head s1) (S.append (S.tail s1) s2)));
    assert (S.equal (be_of_seq_uint32 (S.append s1 s2))
      (S.append (be_of_uint32 (S.head s1)) (be_of_seq_uint32 (S.append (S.tail s1) s2))));
    be_of_seq_uint32_append (S.tail s1) s2
  end

[@(deprecated "FStar.Endianness.be_of_seq_uint32_base")]
let be_of_seq_uint32_base (s1: S.seq U32.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 4 /\
    be_to_n s2 = U32.v (S.index s1 0)))
  (ensures (S.equal s2 (be_of_seq_uint32 s1)))
  [ SMTPat (be_to_n s2 = U32.v (S.index s1 0)) ]
=
  ()

[@(deprecated "FStar.Endianness.le_of_seq_uint32_append")]
let rec le_of_seq_uint32_append (s1 s2: S.seq U32.t): Lemma
  (ensures (
    S.equal (le_of_seq_uint32 (S.append s1 s2))
      (S.append (le_of_seq_uint32 s1) (le_of_seq_uint32 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (le_of_seq_uint32 s1) (le_of_seq_uint32 s2)) ]
=
  Classical.forall_intro_2 (tail_cons #U32.t); // TODO: this is a local pattern, remove once tail_cons lands in FStar.Seq.Properties
  if S.length s1 = 0 then begin
    assert (S.equal (le_of_seq_uint32 s1) S.empty);
    assert (S.equal (S.append s1 s2) s2);
    ()
  end else begin
    assert (S.equal (S.append s1 s2) (S.cons (S.head s1) (S.append (S.tail s1) s2)));
    assert (S.equal (le_of_seq_uint32 (S.append s1 s2))
      (S.append (le_of_uint32 (S.head s1)) (le_of_seq_uint32 (S.append (S.tail s1) s2))));
    le_of_seq_uint32_append (S.tail s1) s2
  end

[@(deprecated "FStar.Endianness.le_of_seq_uint32_base")]
let le_of_seq_uint32_base (s1: S.seq U32.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 4 /\
    le_to_n s2 = U32.v (S.index s1 0)))
  (ensures (S.equal s2 (le_of_seq_uint32 s1)))
  [ SMTPat (le_to_n s2 = U32.v (S.index s1 0)) ]
=
  ()

[@(deprecated "FStar.Endianness.be_of_seq_uint64_append")]
let rec be_of_seq_uint64_append (s1 s2: S.seq U64.t): Lemma
  (ensures (
    S.equal (be_of_seq_uint64 (S.append s1 s2))
      (S.append (be_of_seq_uint64 s1) (be_of_seq_uint64 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (be_of_seq_uint64 s1) (be_of_seq_uint64 s2)) ]
=
  Classical.forall_intro_2 (tail_cons #U64.t); // TODO: this is a local pattern, remove once tail_cons lands in FStar.Seq.Properties
  if S.length s1 = 0 then begin
    assert (S.equal (be_of_seq_uint64 s1) S.empty);
    assert (S.equal (S.append s1 s2) s2);
    ()
  end else begin
    assert (S.equal (S.append s1 s2) (S.cons (S.head s1) (S.append (S.tail s1) s2)));
    assert (S.equal (be_of_seq_uint64 (S.append s1 s2))
      (S.append (be_of_uint64 (S.head s1)) (be_of_seq_uint64 (S.append (S.tail s1) s2))));
    be_of_seq_uint64_append (S.tail s1) s2
  end

[@(deprecated "FStar.Endianness.be_of_seq_uint64_base")]
let be_of_seq_uint64_base (s1: S.seq U64.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 8 /\
    be_to_n s2 = U64.v (S.index s1 0)))
  (ensures (S.equal s2 (be_of_seq_uint64 s1)))
  [ SMTPat (be_to_n s2 = U64.v (S.index s1 0)) ]
=
  ()

[@(deprecated "FStar.Endianness.seq_uint32_of_be_be_of_seq_uint32")]
let rec seq_uint32_of_be_be_of_seq_uint32 (n: nat) (s: S.seq U32.t) : Lemma
  (requires (n == S.length s))
  (ensures (seq_uint32_of_be n (be_of_seq_uint32 s) `S.equal` s))
  (decreases n)
  [SMTPat (seq_uint32_of_be n (be_of_seq_uint32 s))]
= if n = 0
  then ()
  else begin
    assert (s `S.equal` S.cons (S.head s) (S.tail s));
    seq_uint32_of_be_be_of_seq_uint32 (n - 1) (S.tail s);
    let s' = be_of_seq_uint32 s in
    S.lemma_split s' 4;
    S.lemma_append_inj (S.slice s' 0 4) (S.slice s' 4 (S.length s')) (be_of_uint32 (S.head s)) (be_of_seq_uint32 (S.tail s))
  end

[@(deprecated "FStar.Endianness.be_of_seq_uint32_seq_uint32_of_be")]
let rec be_of_seq_uint32_seq_uint32_of_be (n: nat) (s: S.seq U8.t) : Lemma
  (requires (4 * n == S.length s))
  (ensures (be_of_seq_uint32 (seq_uint32_of_be n s) `S.equal` s))
  (decreases n)
  [SMTPat (be_of_seq_uint32 (seq_uint32_of_be n s))]
= if n = 0
  then ()
  else begin
    S.lemma_split s 4;
    be_of_seq_uint32_seq_uint32_of_be (n - 1) (S.slice s 4 (S.length s));
    let s' = seq_uint32_of_be n s in
    let hd, tl = S.split s 4 in
    assert (S.head s' == uint32_of_be hd);
    tail_cons (uint32_of_be hd) (seq_uint32_of_be (n - 1) tl);
    assert (S.tail s' == seq_uint32_of_be (n - 1) tl);
    let s'' = be_of_seq_uint32 s' in
    S.lemma_split s'' 4;
    S.lemma_append_inj (S.slice s'' 0 4) (S.slice s'' 4 (S.length s'')) (be_of_uint32 (S.head s')) (be_of_seq_uint32 (S.tail s'));
    n_to_be_be_to_n 4ul hd
  end

[@(deprecated "FStar.Endianness.slice_seq_uint32_of_be")]
let slice_seq_uint32_of_be (n: nat) (s: S.seq U8.t) (lo: nat) (hi: nat) : Lemma
  (requires (4 * n == S.length s /\ lo <= hi /\ hi <= n))
  (ensures (S.slice (seq_uint32_of_be n s) lo hi) `S.equal` seq_uint32_of_be (hi - lo) (S.slice s (4 * lo) (4 * hi)))
= ()

[@(deprecated "FStar.Endianness.be_of_seq_uint32_slice")]
let be_of_seq_uint32_slice (s: S.seq U32.t) (lo: nat) (hi: nat) : Lemma
  (requires (lo <= hi /\ hi <= S.length s))
  (ensures (be_of_seq_uint32 (S.slice s lo hi) `S.equal` S.slice (be_of_seq_uint32 s) (4 * lo) (4 * hi)))
= slice_seq_uint32_of_be (S.length s) (be_of_seq_uint32 s) lo hi
