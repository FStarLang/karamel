module BoolMatches

#lang-pulse
open Pulse
module Comment = Pulse.Lib.Comment

// The 'unused' stuff is to use the variable v and therefore prevent F*
// from emitting EIfThenElse. We want to test EMatch.
// CInline preserves the boolean constants.
// Inlining uu__ into the scrutinee must not cause the callback to be dropped,
// even if it appears under && false or || true.
fn and_false (i: unit -> fn returns bool) returns bool {
  let uu__ = i ();
  let b = ([@@CInline] let x = false in x);
  match (uu__ && b) {
    true -> { true }
    v -> {
      let unused = Comment.comment_gen "match value" v "";
      false
    }
  }
}

fn or_true (i: unit -> fn returns bool) returns bool {
  let uu__ = i ();
  let b = ([@@CInline] let x = true in x);
  match (uu__ || b) {
    true -> { true }
    v -> {
      let unused = Comment.comment_gen "match value" v "";
      false
    }
  }
}

fn nested_or (i: unit -> fn returns bool) returns bool {
  let uu__ = i ();
  let f = ([@@CInline] let x = false in x);
  let t = ([@@CInline] let x = true in x);
  match ((uu__ && f) || t) {
    true -> { true }
    v -> {
      let unused = Comment.comment_gen "match value" v "";
      false
    }
  }
}

fn nested_and (i: unit -> fn returns bool) returns bool {
  let uu__ = i ();
  let f = ([@@CInline] let x = false in x);
  let t = ([@@CInline] let x = true in x);
  match ((uu__ || t) && f) {
    true -> { true }
    v -> {
      let unused = Comment.comment_gen "match value" v "";
      false
    }
  }
}

// Pure scrutinees should still fold to constants.
fn pure_and (b: bool) returns bool {
  let f = ([@@CInline] let x = false in x);
  match (b && f) {
    true -> { true }
    v -> {
      let unused = Comment.comment_gen "match value" v "";
      false
    }
  }
}

fn pure_or (b: bool) returns bool {
  let t = ([@@CInline] let x = true in x);
  match (b || t) {
    true -> { true }
    v -> {
      let unused = Comment.comment_gen "match value" v "";
      false
    }
  }
}
