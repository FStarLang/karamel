module BufferOps

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
open LowStar.BufferOps

let read (p: B.pointer UInt32.t): HST.Stack UInt32.t
  (fun h -> B.live h p) (fun _ _ _ -> True)
= !*p

let write (p: B.pointer UInt32.t) (v: UInt32.t): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= p *= v

let read64 (p: B.pointer UInt64.t): HST.Stack UInt64.t
  (fun h -> B.live h p) (fun _ _ _ -> True)
= !*p

let read_poly (#a: Type0) (p: B.pointer a): HST.Stack a
  (fun h -> B.live h p) (fun _ _ _ -> True)
= !*p

let read_unit (p: B.pointer unit): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= !*p

let write_unit (p: B.pointer unit): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= p *= ()

type pair = { first: UInt32.t; second: UInt32.t }

// Pointer operators and array accesses denote the same cell at index zero.
let update (p: B.pointer pair) (v: UInt32.t): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= p *= { !*p with first = v }

let update_from_array (p: B.pointer pair) (v: UInt32.t): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= p *= { B.index p 0ul with first = v }

let update_to_array (p: B.pointer pair) (v: UInt32.t): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= B.upd p 0ul { !*p with first = v }

// Keep actual function-pointer calls: the operators also need ordinary bodies.
type reader = p:B.pointer UInt32.t -> HST.Stack UInt32.t
  (fun h -> B.live h p) (fun _ _ _ -> True)

type writer = p:B.pointer UInt32.t -> v:UInt32.t -> HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)

let apply_reader (f: reader) (p: B.pointer UInt32.t): HST.Stack UInt32.t
  (fun h -> B.live h p) (fun _ _ _ -> True)
= f p

let apply_writer (f: writer) (p: B.pointer UInt32.t) (v: UInt32.t): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= f p v

let read_indirect (p: B.pointer UInt32.t): HST.Stack UInt32.t
  (fun h -> B.live h p) (fun _ _ _ -> True)
= apply_reader ( !* ) p

let write_indirect (p: B.pointer UInt32.t) (v: UInt32.t): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= apply_writer ( *= ) p v

let write_curried (p: B.pointer UInt32.t) (v: UInt32.t): HST.Stack unit
  (fun h -> B.live h p) (fun _ _ _ -> True)
= (( *= ) p) v

// Evaluating the destination must happen exactly once, including for reads.
let destination (count: B.pointer UInt32.t) (p: B.pointer UInt32.t): HST.Stack (B.pointer UInt32.t)
  (fun h -> B.live h count /\ B.live h p)
  (fun _ r h -> B.live h count /\ B.live h r)
= count *= UInt32.add_mod !*count 1ul;
  p

let read_effectful (count: B.pointer UInt32.t) (p: B.pointer UInt32.t): HST.Stack UInt32.t
  (fun h -> B.live h count /\ B.live h p) (fun _ _ _ -> True)
= !*(destination count p)

let write_effectful (count: B.pointer UInt32.t) (p: B.pointer UInt32.t) (v: UInt32.t): HST.Stack unit
  (fun h -> B.live h count /\ B.live h p) (fun _ _ _ -> True)
= destination count p *= v

let main (): HST.Stack Int32.t
  (fun _ -> True) (fun _ _ _ -> True)
= HST.push_frame ();
  let p = B.alloca 1ul 1ul in
  write p 2ul;
  let direct = read p in
  write_indirect p 3ul;
  let indirect = read_indirect p in
  write_curried p 4ul;
  let curried = read_poly p in
  let count = B.alloca 0ul 1ul in
  write_effectful count p 5ul;
  let effectful = read_effectful count p in
  let calls = !*count in
  let q = B.alloca { first = 11ul; second = 22ul } 1ul in
  update q 33ul;
  let a = !*q in
  update_from_array q 44ul;
  let b = !*q in
  update_to_array q 55ul;
  let c = !*q in
  let wide = B.alloca 123uL 1ul in
  let wide_value = read64 wide in
  let ok = direct = 2ul && indirect = 3ul && curried = 4ul &&
    effectful = 5ul && calls = 2ul &&
    a.first = 33ul && a.second = 22ul &&
    b.first = 44ul && b.second = 22ul &&
    c.first = 55ul && c.second = 22ul && wide_value = 123uL in
  HST.pop_frame ();
  if ok then 0l else 1l
