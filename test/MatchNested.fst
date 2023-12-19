(* Pathological test for accidentally-exponential backtracking in match-reduction. *)
module MatchNested

inline_for_extraction
let swap (#a #b: eqtype) (ab: (a & b)): (b & a) =
  match ab with
  | (a, b) -> (b, a)

let match_nested (r: (int & int)): (int & int) =
  (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap 
  (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap 
  (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap (swap
  (swap r)))))))))))))))))))))))))))))))))))))))))))))))))

let main () = 0l
