module DataTypes

open FStar.Int.Cast
open FStar.HyperStack.ST
open FStar.Ghost

noeq
type t =
  | A: a:UInt32.t -> b:UInt64.t -> t
  | B: c:UInt8.t -> d:UInt8.t -> e:erased UInt8.t -> t

noeq
type u =
  | C: f:UInt32.t -> g:UInt64.t -> u
  | D: h:t -> i:unit -> u

type v = | E | F

let test (): Stack v (fun _ -> true) (fun _ _ _ -> true) =
  E

let something (): Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

let whatever (e: erased UInt8.t): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

inline_for_extraction
let helper x y =
  let open FStar.UInt32 in
  let a = x +%^ y in
  let b = x -%^ y in
  a, b

let destruct (x, y) =
  let x, y = helper x y in
  FStar.UInt32.(x +%^ y)

type point = { x: UInt32.t; y: UInt32.t; z: UInt32.t }

module B = LowStar.Buffer

let f (p: B.buffer point): Stack unit
  (requires (fun h -> B.live h p /\ B.length p = 1))
  (ensures (fun _ _ _ -> True))
=
  let open LowStar.BufferOps in
  p.(0ul) <- ({ p.(0ul) with x = 0ul })

let f' (p: B.buffer point) (r: UInt32.t): Stack UInt32.t
  (requires (fun h -> B.live h p /\ B.length p = 16))
  (ensures (fun _ _ _ -> True))
=
  let open LowStar.BufferOps in
  p.(15ul) <- ({ p.(15ul) with x = 8ul });
  r

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();

  let x = if something () then A 0ul 1uL else B 2uy 3uy (hide 4uy) in
  let y = if something () then C 5ul 6uL else D x () in
  let z = match x, y with
    | A l h, C l' h' ->
        (* Checks that the variables are not mixed up. *)
        FStar.UInt8.(uint32_to_uint8 l -%^ // 0 -
          uint32_to_uint8 l' +%^ // 5 +
          uint64_to_uint8 h -%^ // 1 -
          uint64_to_uint8 h') // 6
    | _, D (B c d e) u ->
        whatever e;
        if something u then
          (* TODO: or-patterns *)
          FStar.UInt8.(c +%^ d)
        else
          42uy
    | B c d e, _ ->
        whatever e;
        FStar.UInt8.(c +%^ d)
    | _, D _ _ ->
        8uy
  in
  TestLib.checku8 z (FStar.UInt8.(0uy -%^ 10uy));

  let x = match test () with E -> C.EXIT_SUCCESS | _ -> C.EXIT_FAILURE in

  pop_frame ();
  x
