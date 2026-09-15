module DeadBranch

open Pulse
#lang-pulse

// Not really impure, but prevents karamel from using ternary
// expressions when extracting foo. This makes sure we test that
// an actual if block with true/false conditions gets simplified.
fn impure (x : int)
  returns int
{ x }

inline_for_extraction
fn foo (b : bool) (x y : int)
  returns int
{
  if (b) { impure x } else { impure y }
}

fn foo1 (x y : int)
  returns int
{
  foo true x y
}

fn foo2 (x y : int)
  returns int
{
  foo false x y
}

fn foo3 (x : int)
  returns int
{
  foo (x <> 0) 0 x
}
