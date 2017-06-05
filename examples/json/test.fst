
let test
  (a: int)
: Tot (
    (b: int) ->
    Stack int
    (requires (fun h -> True))
    (ensures (fun h res h' -> True))
  )
  =
  fun b -> a + b

(*
let test
  (a: int)
: Pure (
    (b: int) ->
    Stack int
    (requires (fun h -> True))
    (ensures (fun h res h' -> True))
  )
  (True)
  ((fun _ -> True))
  =
  fun b -> a + b

let rec parse_exact_string_contents
  (against: string)
: Pure (
    (b: bstring) -> 
    (len: UInt32.t) -> 
    Stack bool
    (requires (fun h -> string_buffer_valid h b len))
    (ensures (fun h res h' -> parse_exact_string_contents_postcond against b len h res h'))
  )
  (requires True)
  (ensures (fun v -> True))
  (decreases (Seq.length against))
= if
    Seq.length against = 0
  then
    let f
      (b: bstring)
      (len: UInt32.t)
    : Stack bool
      (requires (fun h -> string_buffer_valid h b len))
      (ensures (fun h res h' -> parse_exact_string_contents_postcond against b len h res h'))
    = true
    in
    f
  else
    let c = Seq.head against in
    let _ : squash (Seq.length (Seq.tail against) < Seq.length against) = () in
    let recurse = parse_exact_string_contents (Seq.tail against) in
    let f
      (b: bstring)
      (len: UInt32.t)
    : Stack bool
      (requires (fun h -> string_buffer_valid h b len))
      (ensures (fun h res h' -> parse_exact_string_contents_postcond against b len h res h'))
    = if
        len = 0ul
      then
        false
      else if
        Buffer.index b 0ul = c
      then
        let len' = FStar.UInt32.(len -^ 1ul) in
        let b' = Buffer.sub b 1ul len' in
        recurse b' len'
      else
        false
    in
    f
*)

(* // OK
let rec parse_exact_string_contents
  (against: string)
  (b: bstring)
  (len: UInt32.t)
: Stack bool
  (requires (fun h -> string_buffer_valid h b len))
  (ensures (fun h res h' -> parse_exact_string_contents_postcond against b len h res h'))
= if
    Seq.length against = 0
  then
    true
  else
    let h = ST.get () in
    let c = Seq.head against in
    if
      len = 0ul
    then
      false
    else if
      Buffer.index b 0ul = c
    then
      let len' = FStar.UInt32.(len -^ 1ul) in
      let b' = Buffer.sub b 1ul len' in
      parse_exact_string_contents (Seq.tail against) b' len'
    else
      false
*)

(* // OK
let rec parse_exact_string_contents
  (against: string)
: Tot (
    (b: bstring) -> 
    (len: UInt32.t) -> 
    Stack bool
    (requires (fun h -> string_buffer_valid h b len))
    (ensures (fun h res h' -> parse_exact_string_contents_postcond against b len h res h'))
  )
= if
    Seq.length against = 0
  then
    let f
      (b: bstring)
      (len: UInt32.t)
    : Stack bool
      (requires (fun h -> string_buffer_valid h b len))
      (ensures (fun h res h' -> parse_exact_string_contents_postcond against b len h res h'))
    = true
    in
    f
  else
    let c = Seq.head against in
    let recurse = parse_exact_string_contents (Seq.tail against) in
    let f
      (b: bstring)
      (len: UInt32.t)
    : Stack bool
      (requires (fun h -> string_buffer_valid h b len))
      (ensures (fun h res h' -> parse_exact_string_contents_postcond against b len h res h'))
    = if
        len = 0ul
      then
        false
      else if
        Buffer.index b 0ul = c
      then
        let len' = FStar.UInt32.(len -^ 1ul) in
        let b' = Buffer.sub b 1ul len' in
        recurse b' len'
      else
        false
    in
    f
*)

let rec test2 () : Stack False (requires (fun _ -> True)) (ensures (fun _ _ _ -> False)) = test2 ()

let rec test3 () : Tot (unit ->
     Stack False (requires (fun _ -> True)) (ensures (fun _ _ _ -> False))) = test3 ()


noeq type y = {
  k: (unit ->
     Stack False (requires (fun _ -> True)) (ensures (fun _ _ _ -> False)))
}

(* // KO (as expected)
let rec test4 () : Tot y
= test4 ()
*)

let rec test5 (n: nat) : Tot y = if n = 0 then let r = { k = test3 () } in r else test5 (n-1) 
