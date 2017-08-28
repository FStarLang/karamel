module UseBytes

open FStar.HyperStack.ST

assume val use_bytes : Platform.Bytes.lbytes 0 -> ST unit (fun _ -> True) (fun _ _ _ -> True)

let main : unit -> ST unit (fun _ -> True) (fun _ _ _ -> True) =
  fun () -> let empty = Platform.Bytes.empty_bytes
         in use_bytes empty
