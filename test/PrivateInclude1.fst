module PrivateInclude1

assume val foobar: FStar.Int32.t -> FStar.Int32.t

let f () =
  foobar 0l `FStar.Int32.add` 0l
