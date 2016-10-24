module DataTypes

open FStar.Int.Cast

type t =
  | A: a:Int32.t -> b:Int64.t -> t
  | B: c:Int8.t -> d:Int8.t -> e:Int8.t -> t

type u =
  | C: f:Int32.t -> g:Int64.t -> u
  | D: h:t -> u

let something (): ST.Stack bool (fun _ -> true) (fun _ _ _ -> true) =
  true

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  ST.Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  let x = if something () then A 0l 1L else B 2y 3y 4y in
  let y = if something () then C 5l 6L else D x in
  let z = match x, y with
    | A l h, C l' h' ->
        (* Checks that the variables are not mixed up. *)
        FStar.Int8 (int32_to_int8 l -%^ // 0 -
          int32_to_int8 l' +%^ // 5 +
          int64_to_int8 h -%^ // 1 -
          int64_to_int8 h') // 6
    | _, D (B c d e) ->
        (* TODO: or-patterns *)
        FStar.Int8 (c +%^ d +%^ e)
    | B c d e, _ ->
        FStar.Int8 (c +%^ d +%^ e)
    | _, D _ ->
        8y
  in
  TestLib.check (int8_to_int32 z) (-10l);
  pop_frame ();
  C.exit_success
