module InlineShortCircuit

#lang-pulse
open Pulse

// The call must happen even when the right operand is skipped.
fn and_rhs (b : bool) (i : unit -> fn returns bool)
  returns bool
{
  let uu__ = i ();
  b && uu__
}

fn or_rhs (b : bool) (i : unit -> fn returns bool)
  returns bool
{
  let uu__ = i ();
  b || uu__
}

// The left operand is always evaluated, so these calls may inline.
fn and_lhs (b : bool) (i : unit -> fn returns bool)
  returns bool
{
  let uu__ = i ();
  uu__ && b
}

fn or_lhs (b : bool) (i : unit -> fn returns bool)
  returns bool
{
  let uu__ = i ();
  uu__ || b
}

// Being the left operand of the inner operator is not enough.
fn nested_rhs (b c : bool) (i : unit -> fn returns bool)
  returns bool
{
  let uu__ = i ();
  b && (uu__ || c)
}

fn nested_lhs (b c : bool) (i : unit -> fn returns bool)
  returns bool
{
  let uu__ = i ();
  (uu__ && b) || c
}

fn and_false (i : unit -> fn returns bool)
  returns bool
{
  let uu__ = i ();
  false && uu__
}

fn or_true (i : unit -> fn returns bool)
  returns bool
{
  let uu__ = i ();
  true || uu__
}
