module BoolEffects

#lang-pulse
open Pulse

// Keep the constants through F* extraction so KaRaMeL performs the fold.
// Inlining the temporary into the left operand must preserve the callback.
fn and_false (i : unit -> fn returns bool) returns bool {
  let uu__ = i ();
  let b = ([@@CInline] let x = false in x);
  uu__ && b
}

fn or_true (i : unit -> fn returns bool) returns bool {
  let uu__ = i ();
  let b = ([@@CInline] let x = true in x);
  uu__ || b
}

fn match_and_false (i : unit -> fn returns bool) returns bool {
  let uu__ = i ();
  let b = ([@@CInline] let x = false in x);
  if (uu__ && b) { true } else { false }
}

fn match_or_true (i : unit -> fn returns bool) returns bool {
  let uu__ = i ();
  let b = ([@@CInline] let x = true in x);
  if (uu__ || b) { true } else { false }
}
