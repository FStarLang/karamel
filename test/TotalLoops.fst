module TotalLoops

open FStar
open FStar.Buffer
open FStar.HyperStack.ST

let rec fib
  (x: nat)
: GTot nat
= if x < 2 then x else fib (x-1) + fib (x-2)

type t = {
  i: nat;
  fib_pred_i: nat;
  fib_i: nat;
}

let tfib
  (n: nat)
: Pure nat
  (requires True)
  (ensures (fun y -> y == fib n))
= if n = 0
  then 0
  else
    let x = C.Loops.total_while
      (fun x -> if x.i > n then 0 else n - x.i)
      (fun b x -> 1 <= x.i /\ x.i <= n /\ x.fib_pred_i == fib (x.i - 1) /\ x.fib_i == fib x.i /\ (b == false ==> x.i == n))
      (fun x -> if x.i = n then (false, x) else (true, {i = x.i + 1; fib_pred_i = x.fib_i; fib_i = x.fib_pred_i + x.fib_i}))
      ({ i=1; fib_pred_i=0; fib_i=1; })
    in
    x.fib_i

let main () =
  let b = Buffer.createL [6] in
  let x = Buffer.index b 0ul in
  let y = tfib x in
  if y = 8
  then C.EXIT_SUCCESS
  else C.EXIT_FAILURE
