module PassByReference

type foo = { a: Int32.t; b: Int32.t }

let make (a: Int32.t) : foo = { a = a; b = 0l }

let read (x: foo) : Int32.t = x.a

let forward (x: foo) : Int32.t = read x

#lang-pulse
open Pulse

fn assign (p: ref foo) (a: Int32.t)
  preserves live p
{
  p := make a;
}

fn assign_zero (p: larray foo 5) (a: Int32.t)
  preserves live p
{
  Pulse.Lib.Array.pts_to_len p;
  p.(0sz) <- make a;
}

fn assign_middle (p: larray foo 5) (a: Int32.t)
  preserves live p
{
  Pulse.Lib.Array.pts_to_len p;
  p.(2sz) <- make a;
}

fn read_value (x: foo)
  returns Int32.t
{
  x.a
}

fn read_ref (p: ref foo)
  preserves live p
  returns Int32.t
{
  let uu__x = !p;
  read_value uu__x
}

fn read_zero (p: larray foo 5)
  preserves live p
  returns Int32.t
{
  Pulse.Lib.Array.pts_to_len p;
  let uu__x = p.(0sz);
  read_value uu__x
}
