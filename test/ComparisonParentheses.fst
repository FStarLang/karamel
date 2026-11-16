module ComparisonParentheses

module U32 = FStar.UInt32
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

(* With -fparentheses, nested comparisons must not trigger -Wparentheses. *)
let eq_left (a b: U32.t) (c: bool) = (a = b) = c
let neq_left (a b: U32.t) (c: bool) = (a <> b) = c
let lt_left (a b: U32.t) (c: bool) = U32.lt a b = c
let lte_left (a b: U32.t) (c: bool) = U32.lte a b = c
let gt_left (a b: U32.t) (c: bool) = U32.gt a b = c
let gte_left (a b: U32.t) (c: bool) = U32.gte a b = c

let eq_right (a: bool) (b c: U32.t) = a <> (b = c)
let neq_right (a: bool) (b c: U32.t) = a <> (b <> c)
let lt_right (a: bool) (b c: U32.t) = a <> U32.lt b c
let lte_right (a: bool) (b c: U32.t) = a <> U32.lte b c
let gt_right (a: bool) (b c: U32.t) = a <> U32.gt b c
let gte_right (a: bool) (b c: U32.t) = a <> U32.gte b c

let null_configured (p: B.buffer U32.t) (enabled: bool) : HST.Stack bool
  (fun h -> B.live h p) (fun _ _ _ -> True) =
  B.is_null p = enabled

(* Arithmetic and logical expressions need no extra parentheses. *)
let arithmetic (a b c: U32.t) = U32.add_mod a b = c
let logical (a b c: U32.t) = U32.lt a b && U32.lt b c

let main () = 0l
