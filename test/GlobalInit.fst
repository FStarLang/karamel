module GlobalInit

let f () = GlobalInit2.x.a

let main () = if f () = 18ul then 0l else 1l
