module InlineLoopCond

#lang-pulse
open Pulse

divergent fn test (f : unit -> fn returns UInt32.t)
  returns UInt32.t
{
  let uu__  = f ();
  (* Intentionally possibly-infinite loop. The call above
  cannot be inlined into the condition. *)
  while (uu__ <> 0ul) {
    ()
  };
  0ul
}

divergent fn test_ok (x : UInt32.t)
  returns UInt32.t
{
  (* This one could be inlined (it's not at the moment) *)
  let uu__  = x;
  while (uu__ <> 0ul) {
    ()
  };
  0ul
}
