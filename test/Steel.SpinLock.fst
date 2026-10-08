module Steel.SpinLock

module HST = FStar.HyperStack.ST

// Minimal model to exercise KaRaMeL's NoCopies policy for this type name.
noeq type s_lock = { state: UInt32.t }

assume val acquire (x: s_lock) : HST.Stack unit
  (fun _ -> True)
  (fun _ _ _ -> True)
