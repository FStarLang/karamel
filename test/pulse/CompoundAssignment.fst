module CompoundAssignment

#lang-pulse
open Pulse

module U32 = FStar.UInt32

fn test (x : ref U32.t)
  preserves live x
{
  open U32;
  x := !x +%^ 1ul;
  x := 1ul +%^ !x;
  x := !x -%^ 1ul;
  x := 1ul -%^ !x;
  x := !x *%^ 2ul;
  x := 2ul *%^ !x;
  x := !x /^ 2ul;
  x := !x %^ 2ul;
}

fn test2 (x : ref U32.t)
  requires pure (!x <> 0ul)
  preserves live x
{
  open U32;
  x := 2ul /^ !x;
}

fn test3 (x : ref U32.t)
  requires pure (!x <> 0ul)
  preserves live x
{
  open U32;
  x := 2ul %^ !x;
}

fn test_bitwise (x : ref U32.t)
  preserves live x
{
  open U32;
  x := !x &^ 0x0Ful;
  x := !x |^ 0xF0ul;
  x := !x ^^ 0xAAul;
  x := shift_left (!x) 2ul;
  x := shift_right (!x) 1ul;
}
