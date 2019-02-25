module ProperErasure

module G = FStar.Ghost
module I32 = FStar.Int32

noeq
type foo = {
  x: I32.t;
  y: G.erased int;
}

[@ (CPrologue "_Static_assert(sizeof(foo) == 4, \"y not erased\");")]
let main () =
  let e = { x = 0l; y = G.hide 0 } in
  match e with
  | { y = _ } -> e.x
