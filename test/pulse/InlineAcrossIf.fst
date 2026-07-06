module InlineAcrossIf

#lang-pulse
open Pulse

fn basic (b : bool) (i : unit -> fn returns UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let uu__ = i (); // This name triggers inlining.
  let y = (if b then 2ul else 3ul);
  uu__ +%^ y
}

fn basic2 (b : bool) (i : unit -> fn returns UInt32.t)
  (x y : UInt32.t)
  returns UInt32.t
{
  (* This can inline, x and y are local pure variables. *)
  open FStar.UInt32;
  let uu__ = i ();
  let y = (if b then x else y);
  uu__ +%^ y
}

fn basic3 (b : bool)
  (x : UInt32.t)
  returns UInt32.t
{
  (* This could inline, even if uu__ is used "twice", since
  only one branch is executed. However karamel gates inling
  on "AtMost 1" (syntactic) uses, so it won't inline. *)
  open FStar.UInt32;
  let uu__ = x;
  let y = (if b then uu__ +%^ 1ul else uu__ +%^ 2ul);
  y
}

fn should_not_inline1 (b : bool)
  (i1 i2 : unit -> Tot UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let uu__ = i1 ();
  let y = (if b then i2 () else 0ul);
  uu__ +%^ y;
}

fn should_not_inline2 (b : bool)
  (i1 i2 : unit -> Tot UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let uu__ = i1 ();
  let y = (if b then 0ul else i2());
  uu__ +%^ y;
}

fn should_not_inline3 (b : bool)
  (i1 i2 : unit -> Tot UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let uu__ = i1 ();
  let y = (if i2() = 0ul then 0ul else 1ul);
  uu__ +%^ y;
}
