module NoCopiesConst

module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

let forward (x: Steel.SpinLock.s_lock) : HST.Stack unit
  (fun _ -> True)
  (fun _ _ _ -> True)
=
  Steel.SpinLock.acquire x

// Reusing a lock must keep forwarding the same mutable pointer.
let forward_twice (x: Steel.SpinLock.s_lock) : HST.Stack unit
  (fun _ -> True)
  (fun _ _ _ -> True)
=
  forward x;
  forward x

// NoCopies propagates through multiple levels of containing structs.
noeq type lock_wrapper = { lock: Steel.SpinLock.s_lock; value: UInt32.t }
noeq type nested_lock = { inner: lock_wrapper; count: UInt32.t }

let acquire_nested (x: nested_lock) : HST.Stack unit
  (fun _ -> True)
  (fun _ _ _ -> True)
=
  Steel.SpinLock.acquire x.inner.lock

let forward_nested (x: nested_lock) : HST.Stack unit
  (fun _ -> True)
  (fun _ _ _ -> True)
=
  acquire_nested x

// Updating the count must not copy the enclosing record's lock.
noeq type locked_counter = {
  lock: Steel.SpinLock.s_lock;
  count: UInt32.t;
  unchanged: UInt32.t
}

let set_count (p: B.buffer locked_counter) (count: UInt32.t) : HST.Stack unit
  (requires (fun h -> B.live h p /\ B.length p == 1))
  (ensures (fun _ _ _ -> True))
=
  let old = B.index p 0ul in
  B.upd p 0ul { old with count = count }

// With -fnostruct-passing, ordinary struct parameters must remain const.
noeq type plain = { left: UInt32.t; right: UInt32.t }

let read_plain (x: plain) : UInt32.t = x.left
let forward_plain (x: plain) : UInt32.t = read_plain x
