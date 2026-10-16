module LateCleanup

open Pulse
module Box = Pulse.Lib.Box
#lang-pulse

// Stack promotion exposes a trivial let-binding after the regular inliner.
// Eliminate it even when the local has a user-provided name.
fn local_value (x: UInt32.t)
  returns UInt32.t
{
  let mut cell = x;
  !cell
}

fn ingored_value (x: UInt32.t)
  returns UInt32.t
{
  let mut cell = x;
  123ul
}

(* Local variable still remains here *)
fn local_value2 (x: UInt32.t)
  returns UInt32.t
{
  open FStar.UInt32;
  let mut cell = x;
  let uu__tmp = !cell;
  cell := uu__tmp +%^ 123ul;
  !cell
}

// Eliminate named trivial bindings even when the initializer is effectful.
fn named_value (f: unit -> fn returns UInt32.t)
  returns UInt32.t
{
  let result = f ();
  result
}

// Stack promotion can also expose an effectful initializer late in compilation.
fn effectful_value (f: unit -> fn returns UInt32.t)
  returns UInt32.t
{
  let mut cell = f ();
  !cell
}

fn effectful_sequence (f g: unit -> fn returns UInt32.t)
  returns UInt32.t
{
  let result = f ();
  g ();
  result
}

// An allocation still needs its binding for C code generation.
fn allocated_value (x: UInt32.t)
  returns p: Box.box UInt32.t
  ensures Box.pts_to p x
{
  let p = Box.alloc x;
  p
}
