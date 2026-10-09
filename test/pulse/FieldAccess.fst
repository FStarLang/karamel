module FieldAccess

type foo = { a: Int32.t; b: Int32.t }

#lang-pulse
open Pulse

fn read (p: ref foo)
  preserves live p
  returns Int32.t
{
  let uu__x = !p; // uu__ so it inlines
  uu__x.a
}

fn update (p: ref foo) (a: Int32.t)
  preserves live p
{
  let x = !p;
  p := { x with a = a };
}

(* Even if the index is zero, we want to generate an array access, not a
dereference of the pointer. *)
fn read_zero (p: larray foo 5)
  preserves live p
  returns Int32.t
{
  Pulse.Lib.Array.pts_to_len p;
  let uu__x = p.(0sz);
  uu__x.a
}

fn read_middle (p: larray foo 5)
  preserves live p
  returns Int32.t
{
  Pulse.Lib.Array.pts_to_len p;
  let uu__x = p.(2sz);
  uu__x.a
}
