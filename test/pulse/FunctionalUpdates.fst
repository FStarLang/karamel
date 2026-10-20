module FunctionalUpdates

(* Regression coverage for functional record updates: pointer and local stores,
   multiple replacements, snapshots, indices, effects, and aliases. The expected
   C is updated alongside each change to the lowering pass. *)

type foo = { a: Int32.t; b: Int32.t; y: Int32.t; z: Int32.t }

#lang-pulse
open Pulse

fn upd_1_ptr (p: ref foo) (z: Int32.t)
  preserves live p
{
  let x = !p;
  p := { x with z = z };
}

fn upd_2_ptr (p: ref foo) (y z: Int32.t)
  preserves live p
{
  let x = !p;
  p := { x with y = y; z = z };
}

fn upd_2_seq_ptr (p: ref foo) (y z: Int32.t)
  preserves live p
{
  let x = !p;
  p := { x with y = y };
  let x = !p;
  p := { x with z = z };
}

fn upd_1_local (x: foo) (z: Int32.t)
  returns foo
{
  let mut p = x;
  let old = !p;
  p := { old with z = z };
  !p
}

fn upd_1_local_snapshot (x: foo) (z: Int32.t)
  returns Int32.t
{
  let mut p = x;
  let old = !p;
  p := { old with z = z };
  old.z
}

fn upd_2_local (x: foo) (y z: Int32.t)
  returns foo
{
  let mut p = x;
  let old = !p;
  p := { old with y = y; z = z };
  !p
}

fn upd_2_seq_local (x: foo) (y z: Int32.t)
  returns foo
{
  let mut p = x;
  let old = !p;
  p := { old with y = y };
  let old = !p;
  p := { old with z = z };
  !p
}

fn upd_1_local_direct (x: foo) (z: Int32.t)
  returns foo
{
  let mut p = x;
  p := { a = (!p).a; b = (!p).b; y = (!p).y; z = z };
  !p
}

fn upd_1_array (x: foo) (z: Int32.t)
  returns foo
{
  let mut p = [| x; 1sz |];
  let old = p.(0sz);
  p.(0sz) <- { old with z = z };
  p.(0sz)
}

type counters = { first: UInt32.t; second: UInt32.t; untouched: UInt32.t }
type four_counters = { a: UInt32.t; b: UInt32.t; c: UInt32.t; keep: UInt32.t }

(* Zero changed fields. Custard just generates *p = *p and the functional updates
pass does not do anything here. *)
fn unchanged (p: ref counters)
  preserves live p
{
  let old = !p;
  p := { first = old.first; second = old.second; untouched = old.untouched };
}

fn replace_all (p: ref counters) (first second untouched: UInt32.t)
  preserves live p
{
  p := { first; second; untouched };
}

(* Multiple changed fields must remain a whole-record assignment. *)
fn set_two_constants (p: ref four_counters)
  preserves live p
{
  let old = !p;
  p := { old with a = 1ul; b = 2ul };
}

fn set_three_constants (p: ref four_counters)
  preserves live p
{
  let old = !p;
  p := { old with a = 1ul; b = 2ul; c = 3ul };
}

fn set_two_values (p: ref four_counters) (a b: UInt32.t)
  preserves live p
{
  let old = !p;
  p := { old with a; b };
}

(* A read-only first replacement does not enable a multi-field update. *)
fn read_then_set (p: ref counters)
  preserves live p
{
  p := { first = (!p).second; second = 42ul; untouched = (!p).untouched };
}

(* A single changed field can be assigned in place. *)
fn increment_field (p: ref counters)
  preserves live p
{
  p := { first = UInt32.add_mod (!p).first 1ul;
         second = (!p).second; untouched = (!p).untouched };
}

fn set_at_offset (p: array four_counters) (i: SizeT.t)
  preserves live p
  requires pure (SizeT.v i + 1 < Pulse.Lib.Array.length p)
{
  Pulse.Lib.Array.pts_to_len p;
  let old = p.(SizeT.add i 1sz);
  p.(SizeT.add i 1sz) <- { old with a = 1ul; b = 2ul };
  let old = p.(SizeT.add i 1sz);
  p.(SizeT.add i 1sz) <- { old with c = 3ul };
}

fn swap_snapshot (p: ref counters)
  preserves live p
{
  let old = !p;
  p := { old with first = old.second; second = old.first };
}

(* Keeping the snapshot does not protect reads of the live destination. *)
fn swap_mixed (p: ref counters)
  preserves live p
{
  let old = !p;
  p := { first = old.second; second = (!p).first; untouched = old.untouched };
}

(* The same snapshot is used by the replacement and after the write. *)
fn increment_and_return_old (p: ref counters)
  preserves live p
  returns UInt32.t
{
  let old = !p;
  p := { old with first = UInt32.add_mod old.first 1ul };
  old.first
}

fn swap_and_return_old (p: ref counters)
  preserves live p
  returns UInt32.t
{
  let old = !p;
  p := { old with first = old.second; second = old.first };
  old.first
}

fn swap_fields (p: ref counters)
  preserves live p
{
  let first = (!p).first;
  let second = (!p).second;
  p := { first = second; second = first; untouched = (!p).untouched };
}

fn set_and_return_old (p: ref counters) (value: UInt32.t)
  preserves live p
  returns UInt32.t
{
  let old = !p;
  p := { old with first = value };
  old.first
}

fn set_and_return_arg (p: ref counters) (value result: UInt32.t)
  preserves live p
  returns UInt32.t
{
  let old = !p;
  p := { old with first = value };
  result
}

fn set_at_index (p: array counters) (i: SizeT.t) (value: UInt32.t)
  preserves live p
  requires pure (SizeT.v i < Pulse.Lib.Array.length p)
{
  Pulse.Lib.Array.pts_to_len p;
  let old = p.(i);
  p.(i) <- { old with first = value };
}

fn set_at_index_and_return (p: array counters) (i: SizeT.t) (value: UInt32.t)
  preserves live p
  requires pure (SizeT.v i < Pulse.Lib.Array.length p)
  returns UInt32.t
{
  Pulse.Lib.Array.pts_to_len p;
  let old = p.(i);
  p.(i) <- { old with first = value };
  old.first
}

(* Similar-looking indices in different binder scopes must not be equated. *)
fn copy_index (p: array counters) (i j: SizeT.t) (value: UInt32.t)
  preserves live p
  requires pure (SizeT.v i < Pulse.Lib.Array.length p /\
                 SizeT.v j < Pulse.Lib.Array.length p)
  returns UInt32.t
{
  Pulse.Lib.Array.pts_to_len p;
  let old = p.(i);
  p.(j) <- { old with first = value };
  old.first
}

(* i outside the snapshot binder and j inside it have the same de Bruijn index.
   This terminal variant also catches writing the field back to the source cell. *)
fn copy_index_terminal (p: array counters) (i j: SizeT.t) (value: UInt32.t)
  preserves live p
  requires pure (SizeT.v i < Pulse.Lib.Array.length p /\
                 SizeT.v j < Pulse.Lib.Array.length p)
{
  Pulse.Lib.Array.pts_to_len p;
  let old = p.(i);
  p.(j) <- { old with first = value };
}

fn clobber (p: ref counters)
  preserves live p
{
  let old = !p;
  p := { old with first = old.second };
}

(* The callback can change the untouched fields. The whole-record assignment
   must restore their values from the snapshot, even with one replacement. *)
fn not_even_with_a_single_field (p: ref counters)
  (f: unit -> fn preserves live p returns UInt32.t)
  preserves live p
{
  let old = !p;
  p := { old with first = f () };
}

(* Allocation must remain let-bound after hoisting, even with just one use. *)
fn unused_buffer (n: SizeT.t)
  requires pure (SizeT.v n > 0)
{
  let mut b: array UInt32.t = [| n |];
  ();
}

fn increment (p: ref UInt32.t)
  preserves live p
  returns UInt32.t
{
  let old = !p;
  p := UInt32.add_mod old 1ul;
  old
}

(* Once the stack cell is a scalar, reading it still has to precede the call. *)
fn read_before_call (initial: UInt32.t)
  returns UInt32.t
{
  let mut cell = initial;
  let before = !cell;
  let _ = increment cell;
  before
}

(* A call and a later read must not become unordered operands of addition. *)
fn call_before_read (initial: UInt32.t)
  returns UInt32.t
{
  let mut cell = initial;
  let before = !cell;
  let result = increment cell;
  let after = !cell;
  UInt32.add_mod (UInt32.add_mod before result) after
}

(* A mutable copy owns distinct storage even if its address is used just once. *)
fn increment_snapshot (p: ref UInt32.t)
  preserves p |-> 'value
  returns result: UInt32.t
  ensures pure (result == 'value)
{
  let mut snapshot = !p;
  let _ = increment snapshot;
  !p
}

(* Promoted local storage can still be reached through a pointer alias. *)
fn local_swap_alias (first second: UInt32.t)
  returns result: counters
  ensures pure (result.first == second /\ result.second == first)
{
  let mut cell = { first; second; untouched = 17ul };
  let alias = cell;
  let old_first = (!cell).first;
  let old_second = (!cell).second;
  rewrite each cell as alias;
  let untouched = (!alias).untouched;
  alias := { first = old_second; second = old_first; untouched };
  rewrite each alias as cell;
  !cell
}

type indexed_counters = { index: SizeT.t; value: UInt32.t; spare: UInt32.t }

(* Even constant replacements cannot be split if the first write changes the
   index used by later writes. Inlining and stack promotion expose this alias. *)
fn local_index_alias ()
  returns result: indexed_counters
  ensures pure (result.index == 1sz /\ result.value == 2ul)
{
  let mut cell = [| { index = 0sz; value = 0ul; spare = 17ul }; 2sz |];
  let alias = cell;
  assert rewrites_to alias cell;
  alias.((cell.(0sz)).index) <-
    { index = 1sz; value = 2ul;
      spare = (alias.((cell.(0sz)).index)).spare };
  cell.(0sz)
}

type nested_fields = { left: UInt32.t; right: UInt32.t }
type nested_record = { fields: nested_fields; tag: UInt32.t }

(* Lowering the outer update exposes an assignment to the inner record. The
   later traversal that marks mutable fields must not lower that assignment
   again, after it has already visited the inner record's type declaration. *)
fn nested_update (p: ref nested_record)
  preserves live p
{
  p := { fields = { left = UInt32.add_mod (!p).fields.left 1ul;
                   right = (!p).fields.right };
         tag = (!p).tag };
}

fn nested_update_local (initial: nested_record) (value: UInt32.t)
  returns nested_record
{
  let mut p = initial;
  p := { fields = { left = value; right = (!p).fields.right };
         tag = (!p).tag };
  !p
}
