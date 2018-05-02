module DataTypes

open FStar.Int.Cast
open FStar.HyperStack.ST
open FStar.Ghost

type t =
  | A: a:UInt32.t -> b:UInt64.t -> t
  | B: c:UInt8.t -> d:UInt8.t -> e:erased UInt8.t -> t

type u =
  | C: f:UInt32.t -> g:UInt64.t -> u
  | D: h:t -> i:unit -> u

let something (): Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

let whatever (e: erased UInt8.t): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  ()

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

  pop_frame ();
  C.EXIT_SUCCESS
