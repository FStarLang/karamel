module Ternary

#lang-pulse
open Pulse
module U32 = FStar.UInt32

let u32min (x y : U32.t) =
  let open U32 in
  if x <^ y then x else y

inline_for_extraction noextract
let u32min' (x y : U32.t) =
  let open U32 in
  if x <^ y then x else y

let test2 (x y w z : U32.t) =
  let open U32 in
  u32min' x y +%^ u32min' w z

let u32min'' (x y : U32.t) =
  let open U32 in
  let res = if x <^ y then x else y in
  res +%^ 1ul

let u32min''' (x y : U32.t) =
  let open U32 in
  [@@CInline] let res = if x <^ y then x else y in
  res +%^ 1ul

(* This should generate an actual if statement. *)
let call (b : bool) (f g : unit -> U32.t) =
  if b then f () else g ()

(* Nested ternary *)
let u32clamp (x lo hi : U32.t) =
  let open U32 in
  if x <^ lo then lo
  else if x >^ hi then hi
  else x

(* Boolean ternary *)
let is_in_range (x lo hi : U32.t) : bool =
  let open U32 in
  if x <^ lo then false
  else if x >^ hi then false
  else true

(* This should generate an actual if statement. *)
fn actual_if (b : bool) (f g : unit -> stt unit emp (fun _ -> emp))
  {
    if b {
      f ();
    } else {
      g ();
    }
  }
