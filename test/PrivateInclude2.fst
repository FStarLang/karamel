module PrivateInclude2

let foobar () = 0l

let main () = foobar () `FStar.Int32.add` PrivateInclude1.f ()
