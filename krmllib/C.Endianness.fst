module C.Endianness

module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Krml.Endianness
open LowStar.BufferOps

// Byte-level functions
[@(deprecated "LowStar.Endianness.htole16")]
assume val htole16: UInt16.t -> Tot UInt16.t
[@(deprecated "LowStar.Endianness.le16toh")]
assume val le16toh: UInt16.t -> Tot UInt16.t

[@(deprecated "LowStar.Endianness.htole32")]
assume val htole32: UInt32.t -> Tot UInt32.t
[@(deprecated "LowStar.Endianness.le32toh")]
assume val le32toh: UInt32.t -> Tot UInt32.t

[@(deprecated "LowStar.Endianness.htole64")]
assume val htole64: UInt64.t -> Tot UInt64.t
[@(deprecated "LowStar.Endianness.le64toh")]
assume val le64toh: UInt64.t -> Tot UInt64.t

[@(deprecated "LowStar.Endianness.htobe16")]
assume val htobe16: UInt16.t -> Tot UInt16.t
[@(deprecated "LowStar.Endianness.be16toh")]
assume val be16toh: UInt16.t -> Tot UInt16.t

[@(deprecated "LowStar.Endianness.htobe32")]
assume val htobe32: UInt32.t -> Tot UInt32.t
[@(deprecated "LowStar.Endianness.be32toh")]
assume val be32toh: UInt32.t -> Tot UInt32.t

[@(deprecated "LowStar.Endianness.htobe64")]
assume val htobe64: UInt64.t -> Tot UInt64.t
[@(deprecated "LowStar.Endianness.be64toh")]
assume val be64toh: UInt64.t -> Tot UInt64.t

[@(deprecated "LowStar.Endianness.store16_le")]
assume val store16_le:
  b:B.buffer UInt8.t{B.length b == 2} ->
  z:UInt16.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt16.v z))

[@(deprecated "LowStar.Endianness.load16_le")]
assume val load16_le:
  b:B.buffer UInt8.t{B.length b == 2} ->
  Stack UInt16.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt16.v z))


[@(deprecated "LowStar.Endianness.store16_be")]
assume val store16_be:
  b:B.buffer UInt8.t{B.length b == 2} ->
  z:UInt16.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt16.v z))

[@(deprecated "LowStar.Endianness.load16_be")]
assume val load16_be:
  b:B.buffer UInt8.t{B.length b == 2} ->
  Stack UInt16.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt16.v z))


[@(deprecated "LowStar.Endianness.store32_le")]
assume val store32_le:
  b:B.buffer UInt8.t{B.length b == 4} ->
  z:UInt32.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt32.v z))

[@(deprecated "LowStar.Endianness.load32_le")]
assume val load32_le:
  b:B.buffer UInt8.t{B.length b == 4} ->
  Stack UInt32.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt32.v z))


[@(deprecated "LowStar.Endianness.store32_be")]
assume val store32_be:
  b:B.buffer UInt8.t{B.length b == 4} ->
  z:UInt32.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt32.v z))

[@(deprecated "LowStar.Endianness.load32_be")]
assume val load32_be:
  b:B.buffer UInt8.t{B.length b == 4} ->
  Stack UInt32.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt32.v z))


[@(deprecated "LowStar.Endianness.store64_le")]
assume val store64_le:
  b:B.buffer UInt8.t{B.length b == 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt64.v z))

[@(deprecated "LowStar.Endianness.load64_le")]
assume val load64_le:
  b:B.buffer UInt8.t{B.length b == 8} ->
  Stack UInt64.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt64.v z))


[@(deprecated "LowStar.Endianness.load64_be")]
assume val load64_be:
  b:B.buffer UInt8.t{B.length b == 8} ->
  Stack UInt64.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt64.v z))

[@(deprecated "LowStar.Endianness.store64_be")]
assume val store64_be:
  b:B.buffer UInt8.t{B.length b == 8} ->
  z:UInt64.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt64.v z))


[@(deprecated "LowStar.Endianness.load128_le")]
assume val load128_le:
  b:B.buffer UInt8.t{B.length b == 16} ->
  Stack UInt128.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt128.v z))

[@(deprecated "LowStar.Endianness.store128_le")]
assume val store128_le:
  b:B.buffer UInt8.t{B.length b == 16} ->
  z:UInt128.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt128.v z))


[@(deprecated "LowStar.Endianness.load128_be")]
assume val load128_be:
  b:B.buffer UInt8.t{B.length b == 16} ->
  Stack UInt128.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt128.v z))

[@(deprecated "LowStar.Endianness.store128_be")]
assume val store128_be:
  b:B.buffer UInt8.t{B.length b = 16} ->
  z:UInt128.t ->
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt128.v z))


inline_for_extraction
[@(deprecated "LowStar.Endianness.index_32_be")]
let index_32_be (b: B.buffer UInt8.t) (i: UInt32.t):
  Stack UInt32.t
    (requires (fun h ->
      B.live h b /\ B.length b % 4 = 0 /\
      UInt32.v i < B.length b / 4))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (seq_uint32_of_be (B.length b / 4) (B.as_seq h0 b)) (UInt32.v i)))
=
  load32_be (B.sub b FStar.UInt32.(4ul *^ i) 4ul)

inline_for_extraction
[@(deprecated "LowStar.Endianness.index_32_le")]
let index_32_le (b: B.buffer UInt8.t) (i: UInt32.t):
  Stack UInt32.t
    (requires (fun h ->
      B.live h b /\ B.length b % 4 = 0 /\
      UInt32.v i < B.length b / 4))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (seq_uint32_of_le (B.length b / 4) (B.as_seq h0 b)) (UInt32.v i)))
=
  load32_le (B.sub b FStar.UInt32.(4ul *^ i) 4ul)

inline_for_extraction
[@(deprecated "LowStar.Endianness.index_64_be")]
let index_64_be (b: B.buffer UInt8.t) (i: UInt32.t):
  Stack UInt64.t
    (requires (fun h ->
      B.live h b /\ B.length b % 8 = 0 /\
      UInt32.v i < B.length b / 8))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (seq_uint64_of_be (B.length b / 8) (B.as_seq h0 b)) (UInt32.v i)))
=
  load64_be (B.sub b FStar.UInt32.(8ul *^ i) 8ul)

inline_for_extraction
[@(deprecated "LowStar.Endianness.index_64_le")]
let index_64_le (b: B.buffer UInt8.t) (i: UInt32.t):
  Stack UInt64.t
    (requires (fun h ->
      B.live h b /\ B.length b % 8 = 0 /\
      UInt32.v i < B.length b / 8))
    (ensures (fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r = Seq.index (seq_uint64_of_le (B.length b / 8) (B.as_seq h0 b)) (UInt32.v i)))
=
  load64_le (B.sub b FStar.UInt32.(8ul *^ i) 8ul)

#reset-options "--using_facts_from '* -FStar.UInt8 -FStar.UInt16 -FStar.UInt32 -FStar.UInt64 -FStar.Int8 -FStar.Int16 -FStar.Int32 -FStar.Int64'"

[@(deprecated "LowStar.Endianness.interval_4_disjoint")]
let interval_4_disjoint (i j: nat) : Lemma
  (requires (i <> j))
  (ensures (let open FStar.Mul in 4 * i + 4 <= 4 * j \/ 4 * j + 4 <= 4 * i))
= ()

#reset-options "--z3rlimit 16"

inline_for_extraction
[@(deprecated "LowStar.Endianness.upd_32_be")]
let upd_32_be (b: B.buffer UInt8.t) (i: UInt32.t) (v: UInt32.t):
  Stack unit
    (requires (fun h ->
      B.live h b /\ B.length b % 4 = 0 /\
      UInt32.v i < B.length b / 4))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer b) h0 h1) /\
      seq_uint32_of_be (B.length b / 4) (B.as_seq h1 b) `Seq.equal` Seq.upd (seq_uint32_of_be (B.length b / 4) (B.as_seq h0 b)) (UInt32.v i) v
    ))
= let h0 = get () in
  store32_be (B.sub b FStar.UInt32.(4ul *^ i) 4ul) v;
  let h1 = get () in
  let f () : Lemma
    (seq_uint32_of_be (B.length b / 4) (B.as_seq h1 b) `Seq.equal` Seq.upd (seq_uint32_of_be (B.length b / 4) (B.as_seq h0 b)) (UInt32.v i) v)
  = let s0 = B.as_seq h0 b in
    let s1 = B.as_seq h1 b in
    let n = B.length b / 4 in
    assert (4 `Prims.op_Multiply` n == B.length b);
    let s0' = seq_uint32_of_be n s0 in
    let s1' = seq_uint32_of_be n s1 in
    let lo = UInt32.v i in
    let hi = lo + 1 in
    let s2' = Seq.upd s0' lo v in
    assert (Seq.length s1' == Seq.length s2');
    let f
      (j: nat)
    : Lemma
      (requires (j < n))
      (ensures (j < n /\ Seq.index s1' j == Seq.index s2' j))
    =
      if j = lo
      then ()
      else begin
        slice_seq_uint32_of_be n s0 j (j + 1);
        slice_seq_uint32_of_be n s1 j (j + 1);
        let bj = B.gsub b (4ul `UInt32.mul` UInt32.uint_to_t j) 4ul in
        let sj0 = seq_uint32_of_be 1 (B.as_seq h0 bj) in
        let sj1 = seq_uint32_of_be 1 (B.as_seq h1 bj) in
        assert (Seq.index s1' j == Seq.index sj1 0);
        assert (Seq.index s0' j == Seq.index sj0 0);
        interval_4_disjoint j lo;
        ()
      end
    in
    Classical.forall_intro (Classical.move_requires f)
  in
  f ()
