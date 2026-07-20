module Inline

#lang-pulse
open Pulse

assume val g :  fn (_ : unit) returns UInt32.t

fn basic (i : unit -> fn returns UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let uu__ = i (); // This name triggers inlining.
  uu__
}

fn chain (i : unit -> fn returns UInt32.t)
  (f : UInt32.t -> fn returns UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let uu__ = i ();
  f uu__
}

fn chain_ignore (i : unit -> fn returns UInt32.t)
  (f : UInt32.t -> fn returns UInt32.t)
{
  open FStar.UInt32;
  let uu__ = i ();
  let _ = f uu__;
  ()
}

fn chain_ignore' (i : unit -> fn returns UInt32.t)
  (f : UInt32.t -> fn returns UInt32.t)
{
  open FStar.UInt32;
  let uu__ = i ();
  let x = f uu__; (* x should remain in the C code *)
  ()
}

fn chain_ignore'' (i : unit -> fn returns UInt32.t)
  (f : UInt32.t -> fn returns UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let uu__ = i ();
  let uu__ = f uu__;
  (* ^ should remain since we call g() after *)
  g();
  uu__
}

fn tst (shared : UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let uu__k = shared /^ 100ul;
  let mut i = 0ul;
  while (!i <^ uu__k)
    invariant live i
    invariant pure (v (!i) <= v uu__k)
    decreases (Prims.op_Subtraction (v uu__k) (v (!i)))
  {
    i := !i +^ 1ul;
  };
  1ul
}

fn order (f : unit -> fn returns UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  (* The call to g() can be inlined in the sum,
     but not the call to f(). There is no guaranteed
     ordering if we have f() + g(). *)
  let uu__1 = f ();
  let uu__2 = g ();
  uu__1 +%^ uu__2
}

fn test_array_access
  (a : larray UInt32.t 200)
  (r : ref SizeT.t)
  preserves live a
  preserves r |-> 23sz
  returns UInt32.t
{
  Pulse.Lib.Array.pts_to_len a;
  open FStar.SizeT;
  // g ();
  let uu__ = !r;
  let uu__ = a.(uu__);
  uu__
}
