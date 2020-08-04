module Layered

open FStar.HyperStack.ST
module U32 = FStar.UInt32
module HS = FStar.HyperStack

inline_for_extraction
type context =
  | Context

let pair = context & HS.mem

inline_for_extraction type pre_t = st_pre_h pair
inline_for_extraction type post_t (a:Type) = a -> pair -> Type0
inline_for_extraction type wp_t (a:Type) = wp:(post_t a -> pre_t){
  forall p q. (forall x s. p x s ==> q x s) ==> (forall s. wp p s ==> wp q s)
}

inline_for_extraction
type repr (a:Type) (wp:wp_t a) =
  c:context -> STATE a (fun (p:st_post_h _ a) (h0:HS.mem) ->
    wp (fun x (c', h1) -> (c' == c /\ equal_domains h0 h1) ==> p x h1) (c, h0))

unfold
let return_wp (#a:Type) (x:a) : wp_t a = fun p s -> p x s

inline_for_extraction
let return (a:Type) (x:a)
  : repr a (return_wp x)
  = fun _ -> x

unfold
let bind_wp (#a:Type) (#b:Type) (wp_f:wp_t a) (wp_g:a -> wp_t b)
  : wp_t b
  = fun p -> wp_f (fun x -> wp_g x p)

inline_for_extraction
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
  : repr b (bind_wp wp_f wp_g)
  = fun c ->
    let x = f c in
    g x c

inline_for_extraction
let subcomp (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f) 
  : Pure (repr a wp_g)
      (requires forall p s. wp_g p s ==> wp_f p s)
      (ensures fun _ -> True)
  = f

unfold
let if_then_else_wp (#a:Type) (wp_f wp_g:wp_t a) (p:bool)
  : wp_t a
  = fun post s -> (p ==> wp_f post s) /\ ((~ p) ==> wp_g post s)

inline_for_extraction
let if_then_else (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f) (g:repr a wp_g)
  (p:bool)
  : Type
  = repr a (if_then_else_wp wp_f wp_g p)

reifiable reflectable
layered_effect {
  BUG : a:Type -> wp_t a -> Effect
  with
  repr           = repr;
  return         = return;
  bind           = bind;
  subcomp        = subcomp;
  if_then_else   = if_then_else
}

inline_for_extraction noextract
let get_ctx () : BUG context (fun p (c, h) -> p c (c, h))
  = BUG?.reflect (fun c -> c)

//We use ulib/FStar.Monotonic.Pure module to assume the monotonicity of pure wps
//But somehow that doesn't work if I add a call to that lemma inside the defn. of lift_pure
//So adding it here for now
assume WP_mono :
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a). (forall x. p x ==> q x) ==> (wp p ==> wp q))

unfold
let lift_pure_wp (#a:Type) (wp:pure_wp a)
  : wp_t a
  = fun p s -> wp (fun x -> p x s)

inline_for_extraction
let lift_pure (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
  : repr a (lift_pure_wp wp)
  = fun s -> f ()

sub_effect PURE ~> BUG = lift_pure

inline_for_extraction
let test () : BUG U32.t (fun p tup -> p 5ul tup)
  = 5ul

let main ()
  : ST U32.t (fun _ -> True) (fun _ _ _ -> True) =
  let ctx = Context in
  let test_ret = reify (test ()) ctx in
  test_ret

