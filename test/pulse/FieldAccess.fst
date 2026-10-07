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
