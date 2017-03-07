module JSONParser.Impl

module Spec = JSONParser.Spec

unfold
inline_for_extraction
let op_Plus_Hat = UInt32.op_Plus_Hat

unfold
inline_for_extraction
let op_Subtraction_Hat = UInt32.op_Subtraction_Hat

type char = Spec.char
type sstring = Spec.sstring
type lstring = Spec.lstring

type string_ptr_field =
| StringLength
| StringPtr

type bstring = Buffer.buffer char

unfold
type string_ptr_struct = DependentMap.t _ (function
  | StringLength -> UInt32.t
  | StringPtr -> bstring
)

unfold
type string_ptr = Struct.struct_ptr string_ptr_struct

unfold
let string_buffer_valid (h: HyperStack.mem) (b: bstring) (n: UInt32.t): GTot Type0 =
  Buffer.live h b /\
  UInt32.v n = Buffer.length b

unfold
let string_ptr_struct_valid (h: HyperStack.mem) (s: string_ptr_struct) : GTot Type0 =
  let b: Buffer.buffer char = DependentMap.sel s StringPtr in
  string_buffer_valid h b (DependentMap.sel s StringLength)

unfold
let string_ptr_struct_value (h: HyperStack.mem) (s: string_ptr_struct {string_ptr_struct_valid h s}) : GTot sstring =
  Buffer.as_seq h (DependentMap.sel s StringPtr)

unfold
let string_ptr_valid (h: HyperStack.mem) (s: string_ptr) : GTot Type0 =
  Struct.live h s /\  
  string_ptr_struct_valid h (Struct.as_value h s) /\
  Buffer.disjoint (Struct.as_value h (Struct.gfield s StringPtr)) (Struct.as_buffer s)

unfold
let string_ptr_value (h: HyperStack.mem) (s: string_ptr {string_ptr_valid h s}): GTot sstring =
  string_ptr_struct_value h (Struct.as_value h s)

#reset-options "--z3rlimit 128"

[@"substitute" "c_inline"]
inline_for_extraction
let parse_whitespace
  (b: bstring)
  (len: UInt32.t)
: Stack UInt32.t
  (requires (fun h -> string_buffer_valid h b len))
  (ensures (fun h i h' ->
    h' == h /\
    string_buffer_valid h b len /\
    UInt32.v i <= UInt32.v len /\ (
      let s = Buffer.as_seq h b in
      Spec.gparse_whitespace s == Seq.slice s (UInt32.v i) (UInt32.v len)
  )))
= let h0: HyperStack.mem = ST.get () in
  let s () : GTot sstring = Buffer.as_seq h0 b in
  let inv (h: HyperStack.mem) (i: nat) (b: bool) : GTot Type0 =
    h == h0 /\
    i <= UInt32.v len /\ (
      let value = Spec.gparse_whitespace (s ()) in
      if 
        b
      then (
        1 <= i /\
        value == Seq.slice (s ()) (i - 1) (UInt32.v len)
      )
      else
        value == Spec.gparse_whitespace (Seq.slice (s ()) i (UInt32.v len))
    )
  in
  let body
    (i: UInt32.t {UInt32.v len > UInt32.v i})
  : Stack bool
    (requires (fun h -> inv h (UInt32.v i) false))
    (ensures (fun h1 b h2 -> inv h1 (UInt32.v i) false /\ inv h2 (UInt32.v i + 1) b))
  = let c = Buffer.index b i in
    not (Spec.is_whitespace c)
  in
  let (i, b) = C.Loops.interruptible_for 0ul len inv body in
  if b then (i -^ 1ul) else len

inline_for_extraction
let parse_exact_char
  (c: char)
  (b: bstring)
  (len: UInt32.t)
: Stack UInt32.t
  (requires (fun h -> string_buffer_valid h b len))
  (ensures (fun h i h' ->
    h' == h /\
    string_buffer_valid h b len /\
    UInt32.v i <= UInt32.v len /\ (
      let s = Buffer.as_seq h b in
      Spec.gparse_exact_char c s == (if i = 0ul then None else Some (Seq.slice s (UInt32.v i) (UInt32.v len)))
  )))
= let i_ws = parse_whitespace b len in
  if
    i_ws = len
  then
    0ul
  else
    let c' = Buffer.index b i_ws in
    if c' = c then (i_ws +^ 1ul) else 0ul

inline_for_extraction
let parse_string_contents
  (b: bstring)
  (n: UInt32.t)
: Stack UInt32.t
  (requires (fun h ->
    string_buffer_valid h b n
  ))
  (ensures (fun h n' h' ->
    string_buffer_valid h b n /\
    h' == h /\
    UInt32.v n' <= UInt32.v n /\ (
      let s = Buffer.as_seq h b in
      Spec.gparse_string_contents Seq.createEmpty s == (
        if
	  n' = 0ul
	then
	  None
	else
	  Some (Seq.slice s 0 (UInt32.v n' - 1), Seq.slice s (UInt32.v n') (UInt32.v n))
  ))))
= if
    n = 0ul
  then
    0ul
  else
    let h0 = ST.get () in
    let s () : GTot sstring = Buffer.as_seq h0 b in
    let value () : GTot (option (sstring * sstring)) = Spec.gparse_string_contents Seq.createEmpty (s ()) in
    let inv (h: HyperStack.mem) (i: nat) (b': bool) : GTot Type0 =
      h == h0 /\
      i <= UInt32.v n /\ (
        if
	  b'
	then (
	  1 <= i /\
	  value () == Some (Seq.slice (s ()) 0 (i - 1), Seq.slice (s ()) i (UInt32.v n))
	)
	else if
	  i < UInt32.v n
	then
	  value () == Spec.gparse_string_contents (Seq.slice (s ()) 0 i) (Seq.slice (s ()) i (UInt32.v n))
	else
	  value () == None
      )
    in
    let body
      (i: UInt32.t {0 <= UInt32.v i /\ UInt32.v i < UInt32.v n})
    : Stack bool
      (requires (fun h -> inv h (UInt32.v i) false))
      (ensures (fun h1 b h2 -> inv h1 (UInt32.v i) false /\ inv h2 (UInt32.v i + 1) b))
    = Buffer.index b i = Spec.double_quote
    in
    let _ : squash (Seq.slice (s ()) 0 0 == Seq.createEmpty) =
      Seq.lemma_eq_elim (Seq.slice (s ()) 0 0) (Seq.createEmpty)
    in
    let _ : squash (Seq.slice (s ()) 0 (UInt32.v n) == s ()) =
      Seq.lemma_eq_elim (Seq.slice (s ()) 0 (UInt32.v n)) (s ())
    in
    let (i, b) = C.Loops.interruptible_for 0ul n inv body in
    if b then i else 0ul

inline_for_extraction
let parse_string
  (p: string_ptr)
  (b: bstring)
  (len: UInt32.t)
: Stack UInt32.t
  (requires (fun h -> string_buffer_valid h b len /\ Struct.live h p /\ Buffer.disjoint (Struct.as_buffer p) b))
  (ensures (fun h i h' ->
    string_buffer_valid h b len /\
    Struct.live h p /\
    Buffer.disjoint (Struct.as_buffer p) b /\ (
      let s = Buffer.as_seq h b in
      let value = Spec.gparse_string s in
      if 
        i = 0ul
      then
        (h' == h /\ value == None)
      else (
	string_ptr_valid h' p /\
        Struct.modifies_1 p h h' /\
	string_buffer_valid h' b len /\
	Buffer.as_seq h' b == s /\
	UInt32.v i <= UInt32.v len /\
	(Buffer.sub b 0ul (i -^ 1ul)) `Buffer.includes` (Struct.as_value h' (Struct.gfield p StringPtr)) /\
	value == Some (string_ptr_value h' p, Seq.slice s (UInt32.v i) (UInt32.v len))
  ))))
= let f_char = parse_exact_char Spec.double_quote in
  let i_after_first_quote = f_char b len in
  if
    i_after_first_quote = 0ul
  then
    0ul
  else
    let len_after_first_quote = (len -^ i_after_first_quote) in
    let b_after_first_quote = Buffer.sub b i_after_first_quote len_after_first_quote in
    let i_after_contents = parse_string_contents b_after_first_quote len_after_first_quote in
    if
      i_after_contents = 0ul
    then
      0ul
    else
      let h = ST.get () in
      let len_contents = (i_after_contents -^ 1ul) in
      let _ = Struct.write (Struct.field p StringPtr) (Buffer.sub b_after_first_quote 0ul len_contents) in
      let _ = Struct.write (Struct.field p StringLength) len_contents in
      let h' = ST.get () in
      let _ = Struct.modifies_1_reveal p h h' in
      let _ = Buffer.lemma_reveal_modifies_1 (Struct.as_buffer p) h h' in
      let res = (i_after_first_quote +^ i_after_contents) in
      let _ = Buffer.sub_sub b 0ul (res -^ 1ul) i_after_first_quote len_contents in
      res

unfold
let parse_exact_string_contents_postcond
  (against: lstring)
  (b: bstring)
  (len: UInt32.t)
  (h: HyperStack.mem)
  (res: bool)
  (h': HyperStack.mem)
: GTot Type0
= h' == h /\
  string_buffer_valid h b len /\ (
    let s = Buffer.as_seq h b in
    let value = Spec.gparse_exact_string_contents against s in
    if
      res
    then (
      List.Tot.length against <= UInt32.v len /\
      value == Some (Seq.slice s (List.Tot.length against) (UInt32.v len))
    )
    else
      value == None
  )

let parse_exact_string_contents_ty (against: lstring) : Tot Type =
    (b: bstring) ->
    (len: UInt32.t) -> 
    Stack bool
    (requires (fun h -> string_buffer_valid h b len))
    (ensures (fun h res h' -> parse_exact_string_contents_postcond against b len h res h'))

inline_for_extraction
let parse_exact_string_contents_cons
  (c: char)
  (tl_against: lstring )
  (recurse: parse_exact_string_contents_ty tl_against)
  (b: bstring)
  (len: UInt32.t) 
: Stack bool
  (requires (fun h -> string_buffer_valid h b len))
  (ensures (fun h res h' -> parse_exact_string_contents_postcond (c :: tl_against) b len h res h'))
= let re : parse_exact_string_contents_ty (tl_against) = normalize_term recurse in
  if
    len = 0ul
  then
    false
  else if
    Buffer.index b 0ul = c
  then
    let len' = (len -^ 1ul) in
    let b' = Buffer.sub b 1ul len' in
    re b' len'
  else
    false

inline_for_extraction
let parse_exact_string_contents_nil
  (b: bstring)
  (len: UInt32.t) 
: Stack bool
  (requires (fun h -> string_buffer_valid h b len))
  (ensures (fun h res h' -> parse_exact_string_contents_postcond [] b len h res h'))
= true

inline_for_extraction
let rec parse_exact_string_contents
  (against: lstring)
: Tot (parse_exact_string_contents_ty against)
= match against with
  | [] ->
    parse_exact_string_contents_nil
  | c :: tl_against ->
    let recurse : parse_exact_string_contents_ty tl_against = parse_exact_string_contents tl_against in
    parse_exact_string_contents_cons c tl_against recurse

let parse_exact_string_postcond
  (against: lstring { ~ (List.Tot.mem Spec.double_quote against) } )
  (b: bstring)
  (len: UInt32.t)
  h i h'
: GTot Type0  
= h' == h /\
  string_buffer_valid h b len /\ (
    let s = Buffer.as_seq h b in
    let value = Spec.gparse_exact_string against s in
    if
      i = 0ul
    then
      value = None
    else (
      UInt32.v i <= UInt32.v len /\
      value == Some (Seq.slice s (UInt32.v i) (UInt32.v len))
  ))

inline_for_extraction
let parse_exact_string
  (against: lstring { ~ (List.Tot.mem Spec.double_quote against) } )
  (b: bstring)
  (len: UInt32.t)
: Stack UInt32.t
  (requires (fun h -> string_buffer_valid h b len))
  (ensures (fun h i h' -> parse_exact_string_postcond against b len h i h'))
= let f_char = parse_exact_char Spec.double_quote in
  let f  : parse_exact_string_contents_ty against = (normalize_term (parse_exact_string_contents against)) in
  let i_after_first_quote = f_char b len in
  if
    i_after_first_quote = 0ul
  then
    0ul
  else
    let len_after_first_quote = (len -^ i_after_first_quote) in
    let b_after_first_quote = Buffer.sub b i_after_first_quote len_after_first_quote in
    if
      f b_after_first_quote len_after_first_quote
    then
      let (len_against: UInt32.t { len_against == UInt32.uint_to_t (List.Tot.length against) } ) = UInt32.uint_to_t (normalize_term (List.Tot.length against)) in
      if
        len_after_first_quote = len_against
      then
        0ul
      else if
        Buffer.index b_after_first_quote len_against <> Spec.double_quote
      then
        0ul
      else
        (i_after_first_quote +^ len_against +^ 1ul)
    else
      0ul

(*  // Tests
inline_for_extraction
let against () : Tot lstring = [Char.char_of_int 65; Char.char_of_int 66]

let test18 = 
  normalize_term (parse_exact_string (normalize_term (against ())))
*)

let rec as_type (j: Spec.json_schema) : Tot Type =
  match j with
  | Spec.String -> string_ptr_struct
  | Spec.Object l ->
    DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l) }) (Spec.object_as_type (Spec.Object l) as_type l)

let as_type_object_eq
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
: Lemma
  (requires True)
  (ensures 
   (as_type (Spec.Object l) ==
    DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l) }) (Spec.object_as_type (Spec.Object l) as_type l)))
  [SMTPat (as_type (Spec.Object l))]
= assert_norm (as_type (Spec.Object l) ==
    DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l) }) (Spec.object_as_type (Spec.Object l) as_type l))

let as_type_string: squash (as_type Spec.String == string_ptr_struct) = ()

noeq type object_forall_string_ptr_t
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') ->  Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
: (l_left: list (Spec.key * Spec.json_schema)) ->
  (l_right: list (Spec.key * Spec.json_schema)) ->
  GTot Type0
= | OFSP_nil:
    object_forall_string_ptr_t l forall_string_ptr ptr data [] l
  | OFSP_snoc:
    (l_left: list (Spec.key * Spec.json_schema)) ->
    (s': Spec.key {List.Tot.mem s' (List.Tot.map fst l) }) ->
    (j': Spec.json_schema) ->
    (l_right: list (Spec.key * Spec.json_schema)) ->
    (ofsp_rec: object_forall_string_ptr_t l forall_string_ptr ptr data l_left ((s', j') :: l_right)) ->
    (precond: squash (
      List.Tot.assoc s' (List.Tot.append l_left [(s', j')]) == Some j' /\
      Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
      Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j' /\
      j' << Spec.Object l /\
      forall_string_ptr j' (Struct.gfield ptr s') (DependentMap.sel data s') /\
      l == List.Tot.append l_left ((s', j') :: l_right) /\
      l == List.Tot.append (List.Tot.append l_left [(s', j')]) l_right
    )) ->
    object_forall_string_ptr_t l forall_string_ptr ptr data (List.Tot.append l_left [(s', j')]) l_right

let rec object_forall_string_ptr_t_elim
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
  (o: object_forall_string_ptr_t l forall_string_ptr ptr data l_left l_right)
  (s': Spec.key {List.Tot.mem s' (List.Tot.map fst l) } )
  (j': Spec.json_schema { List.Tot.assoc s' l_left == Some j' } )
: Lemma
  (requires True)
  (ensures (Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\ Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j' /\ j' << Spec.Object l /\ forall_string_ptr j' (Struct.gfield ptr s') (DependentMap.sel data s')))
  (decreases o)
= match o with
  | OFSP_nil -> ()
  | OFSP_snoc l_left_ s_ j_ l_right_ o_ h ->
    let s' : Spec.key = s' in
    let e : option Spec.json_schema = List.Tot.assoc s' l_left_ in
    begin match e with
    | Some j'' ->
      let _ : squash (j'' == j') =
	List.Tot.assoc_append_elim_r s' l_left_ [(s_, j_)]
      in
      object_forall_string_ptr_t_elim l forall_string_ptr ptr data l_left_ ((s_, j_) :: l_right_) o_ s' j'
    | None ->
      let _ : squash (List.Tot.assoc s' (List.Tot.append l_left_ [(s_, j_)]) == List.Tot.assoc s' [(s_, j_)]) =
	List.Tot.assoc_append_elim_l s' l_left_ [(s_, j_)]
      in
      ()
    end

let object_forall_string_ptr_t_inv2
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr1 forall_string_ptr2: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
  (o1: object_forall_string_ptr_t l forall_string_ptr1 ptr data l_left l_right)
  (o2: object_forall_string_ptr_t l forall_string_ptr2 ptr data l_left l_right)
: Lemma
  (requires True)
  (ensures (
    match o1 with
    | OFSP_nil ->
      o2 == OFSP_nil
    | OFSP_snoc l_left1 s1 j1 l_right1 _ _ ->
      OFSP_snoc? o2 /\ (
        let (OFSP_snoc l_left2 s2 j2 l_right2 _ _) = o2 in
        l_left1 == l_left2 /\
        s1 == s2 /\
        j1 == j2 /\
        l_right1 == l_right2
  )))
= match o1 with
  | OFSP_nil -> ()
  | OFSP_snoc l_left1 s1 j1 l_right1 _ _ ->
    begin match o2 with
    | OFSP_snoc l_left2 s2 j2 l_right2 _ _ ->
      List.Tot.append_inv_tail l_right1 (List.Tot.append l_left1 [(s1, j1)]) (List.Tot.append l_left2 [(s2, j2)]);
      List.Tot.append_length_inv_tail l_left1 [(s1, j1)] l_left2 [(s2, j2)]
    end

let rec object_forall_string_ptr_t_eq_append
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
  (o: object_forall_string_ptr_t l forall_string_ptr ptr data l_left l_right)
: Lemma
  (ensures (l == List.Tot.append l_left l_right))
= match o with
  | OFSP_nil ->
    List.Tot.append_l_nil l
  | _ -> ()

let exists_assoc_append
  (#a: eqtype)
  (#b: Type)
  (ll: list (a * b))
  (y: b)
  (lr: list (a * b))
: Lemma
  (requires (exists x . List.Tot.assoc x ll == Some y))
  (ensures (exists x . List.Tot.assoc x (List.Tot.append ll lr) == Some y))
= Classical.exists_elim
    (exists x . List.Tot.assoc x (List.Tot.append ll lr) == Some y)
    #_
    #(fun x -> List.Tot.assoc x ll == Some y)
    ()
    (fun x ->
      let _ = List.Tot.assoc_append_elim_r x ll lr in
      Classical.exists_intro
	(fun x -> List.Tot.assoc x (List.Tot.append ll lr) == Some y)
	x
    )

let rec object_forall_string_ptr_t_implies
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr1 forall_string_ptr2: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
  (o: object_forall_string_ptr_t l forall_string_ptr1 ptr data l_left l_right)
  (ih:
    (j': Spec.json_schema {j' << Spec.Object l}) ->
    (s': Spec.key {
      List.Tot.mem s' (List.Tot.map fst l) /\
      List.Tot.assoc s' l_left == Some j' /\
      Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
      Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j'
    }) ->
    Lemma
    (requires (forall_string_ptr1 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
    (ensures (forall_string_ptr2 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
  )
: Ghost (object_forall_string_ptr_t l forall_string_ptr2 ptr data l_left l_right)
  (requires True)
  (ensures (fun _ -> True))
  (decreases o)
= match o with
  | OFSP_nil -> OFSP_nil
  | OFSP_snoc l_left_ s_ j_ l_right_ o_ h ->
    ih j_ s_;
    let ih'
      (j': Spec.json_schema {j' << Spec.Object l})
      (s': Spec.key {
	List.Tot.mem s' (List.Tot.map fst l) /\
	List.Tot.assoc s' l_left_ == Some j' /\
	Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
	Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j'
      })
    : Lemma
      (requires (forall_string_ptr1 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
      (ensures (forall_string_ptr2 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
    = let _ : squash (List.Tot.assoc s' (List.Tot.append l_left_ [(s_, j_)]) == Some j') =
        List.Tot.assoc_append_elim_r s' l_left_ [(s_, j_)]
      in
      ih j' s'
    in
    OFSP_snoc l_left_ s_ j_ l_right_ (object_forall_string_ptr_t_implies l forall_string_ptr1 forall_string_ptr2 ptr data l_left_ ((s_, j_) :: l_right_) o_ ih') ()

let rec object_forall_string_ptr_t_and
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr1 forall_string_ptr2 forall_string_ptrand: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
  (op: object_forall_string_ptr_t l forall_string_ptr1 ptr data l_left l_right)
  (oq: object_forall_string_ptr_t l forall_string_ptr2 ptr data l_left l_right)
  (ih:
    (j': Spec.json_schema {j' << Spec.Object l}) ->
    (s': Spec.key {
      List.Tot.mem s' (List.Tot.map fst l) /\
      List.Tot.assoc s' l_left == Some j' /\
      Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
      Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j'
    }) ->
    Lemma
    (requires (forall_string_ptr1 j' (Struct.gfield ptr s') (DependentMap.sel data s') /\ forall_string_ptr2 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
    (ensures (forall_string_ptrand j' (Struct.gfield ptr s') (DependentMap.sel data s')))
  )
: Ghost (object_forall_string_ptr_t l forall_string_ptrand ptr data l_left l_right)
  (requires True)
  (ensures (fun _ -> True))
  (decreases op)
= match op with
  | OFSP_nil -> OFSP_nil
  | OFSP_snoc l_leftp sp jp l_rightp op_ hp ->
    object_forall_string_ptr_t_inv2 l forall_string_ptr1 forall_string_ptr2 ptr data l_left l_right op oq;
    let (OFSP_snoc _ _ _ _ oq_ hq) = oq in
    ih jp sp;
    let ih'
      (j': Spec.json_schema {j' << Spec.Object l})
      (s': Spec.key {
	List.Tot.mem s' (List.Tot.map fst l) /\
	List.Tot.assoc s' l_leftp == Some j' /\
	Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
	Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j'
      })
    : Lemma
      (requires (forall_string_ptr1 j' (Struct.gfield ptr s') (DependentMap.sel data s') /\ forall_string_ptr2 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
      (ensures (forall_string_ptrand j' (Struct.gfield ptr s') (DependentMap.sel data s')))
    = let _ : squash (List.Tot.assoc s' (List.Tot.append l_leftp [(sp, jp)]) == Some j') =
        List.Tot.assoc_append_elim_r s' l_leftp [(sp, jp)]
      in
      ih j' s'
    in
    OFSP_snoc l_leftp sp jp l_rightp (object_forall_string_ptr_t_and l forall_string_ptr1 forall_string_ptr2 forall_string_ptrand ptr data l_leftp ((sp, jp) :: l_rightp) op_ oq_ ih' ) ()

let object_forall_string_ptr
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
: GTot Type0
= squash (object_forall_string_ptr_t l forall_string_ptr ptr data l_left l_right)

let rec object_forall_string_ptr_elim
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
  (s': Spec.key {List.Tot.mem s' (List.Tot.map fst l) } )
  (j': Spec.json_schema { List.Tot.assoc s' l_left == Some j' } )
: Lemma
  (requires (object_forall_string_ptr l forall_string_ptr ptr data l_left l_right))
  (ensures (Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\ Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j' /\ j' << Spec.Object l /\ forall_string_ptr j' (Struct.gfield ptr s') (DependentMap.sel data s')))
= let o : squash (object_forall_string_ptr l forall_string_ptr ptr data l_left l_right) = () in
  let o : squash (object_forall_string_ptr_t l forall_string_ptr ptr data l_left l_right) = Squash.join_squash o in
  Squash.bind_squash #_ #(Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\ Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j' /\ j' << Spec.Object l /\ forall_string_ptr j' (Struct.gfield ptr s') (DependentMap.sel data s')) o (fun o ->
      object_forall_string_ptr_t_elim l forall_string_ptr ptr data l_left l_right o s' j'
  )

let object_forall_string_ptr_nil
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
: Lemma
  (ensures (object_forall_string_ptr l forall_string_ptr ptr data [] l))
= Squash.return_squash #(object_forall_string_ptr_t l forall_string_ptr ptr data [] l) OFSP_nil

let object_forall_string_ptr_snoc
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (s': Spec.key {List.Tot.mem s' (List.Tot.map fst l) })
  (j': Spec.json_schema)
  (l_right: list (Spec.key * Spec.json_schema))
: Lemma
  (requires (
    object_forall_string_ptr l forall_string_ptr ptr data l_left ((s', j') :: l_right) /\ (
      (
        Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
        Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j' /\
        j' << Spec.Object l
      ) ==>
      forall_string_ptr j' (Struct.gfield ptr s') (DependentMap.sel data s')
  )))
  (ensures (object_forall_string_ptr l forall_string_ptr ptr data (List.Tot.append l_left [(s', j')]) l_right))
= let x : squash (object_forall_string_ptr_t l forall_string_ptr ptr data l_left ((s', j') :: l_right)) = Squash.join_squash () in
  Squash.map_squash #_ #(object_forall_string_ptr_t l forall_string_ptr ptr data (List.Tot.append l_left [(s', j')]) l_right) x (fun o ->
    let _ : squash (l == List.Tot.append l_left ((s', j') :: l_right)) =
      object_forall_string_ptr_t_eq_append l forall_string_ptr ptr data l_left ((s', j') :: l_right) o      
    in
    let _ : squash (List.Tot.assoc s' l_left == None) =
      match List.Tot.assoc s' l_left with
      | None -> ()
      | Some _ ->
	let _: squash (List.Tot.mem s' (List.Tot.map fst l_left)) =
	  List.Tot.assoc_mem s' l_left
	in
	let _ = List.Tot.map_append fst l_left ((s', j') :: l_right) in
	let _ = List.Tot.noRepeats_append_elim (List.Tot.map fst l_left) (List.Tot.map fst ((s', j') :: l_right)) in
	()
    in
    let _ : squash (List.Tot.assoc s' (List.Tot.append l_left [(s', j')]) == Some j') =
      List.Tot.assoc_append_elim_l s' l_left [(s', j')]
    in
    let _ : squash (List.Tot.assoc s' l == Some j') =
      List.Tot.assoc_append_elim_l s' l_left ((s', j') :: l_right)
    in
    let _ = List.Tot.assoc_precedes s' l j' in
    let _ : squash (Spec.object_as_type (Spec.Object l) as_type l s' == as_type j') =
      Spec.object_as_type_assoc (Spec.Object l) as_type l s'
    in
    let _ = Spec.object_as_type_assoc (Spec.Object l) Spec.as_gtype l s' in
    let _ = List.Tot.append_assoc l_left [(s', j')] l_right in
    OFSP_snoc l_left s' j' l_right o ()
  )

let object_forall_string_ptr_implies
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr1 forall_string_ptr2: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
  (ih:
    (j': Spec.json_schema {j' << Spec.Object l}) ->
    (s': Spec.key {
      List.Tot.mem s' (List.Tot.map fst l) /\
      List.Tot.assoc s' l_left == Some j' /\
      Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
      Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j'
    }) ->
    Lemma
    (requires (forall_string_ptr1 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
    (ensures (forall_string_ptr2 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
  )
: Lemma
  (ensures (
    object_forall_string_ptr l forall_string_ptr1 ptr data l_left l_right ==>
    object_forall_string_ptr l forall_string_ptr2 ptr data l_left l_right
  ))
= Classical.impl_intro (
    let f
      (h: object_forall_string_ptr l forall_string_ptr1 ptr data l_left l_right)
    : Lemma (object_forall_string_ptr l forall_string_ptr2 ptr data l_left l_right)
    = Squash.map_squash
        h
        (fun o -> (object_forall_string_ptr_t_implies l forall_string_ptr1 forall_string_ptr2 ptr data l_left l_right o ih))
    in
    f
  )

let object_forall_string_ptr_equiv
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr1 forall_string_ptr2: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
: Lemma
  (requires (
    forall
    (j': Spec.json_schema {j' << Spec.Object l})
    (s': Spec.key {
      List.Tot.mem s' (List.Tot.map fst l) /\
      List.Tot.assoc s' l_left == Some j' /\
      Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
      Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j'
    })
    .
    forall_string_ptr1 j' (Struct.gfield ptr s') (DependentMap.sel data s') <==> forall_string_ptr2 j' (Struct.gfield ptr s') (DependentMap.sel data s')
  ))
  (ensures (
    object_forall_string_ptr l forall_string_ptr1 ptr data l_left l_right <==>
    object_forall_string_ptr l forall_string_ptr2 ptr data l_left l_right
  ))
= object_forall_string_ptr_implies l forall_string_ptr1 forall_string_ptr2 ptr data l_left l_right (fun _ _ -> ());
  object_forall_string_ptr_implies l forall_string_ptr2 forall_string_ptr1 ptr data l_left l_right (fun _ _ -> ())

let object_forall_string_ptr_and
  (l: list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)})
  (forall_string_ptr1 forall_string_ptr2 forall_string_ptrand: (j': Spec.json_schema {j' << Spec.Object l}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l)))
  (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l))
  (l_left: list (Spec.key * Spec.json_schema))
  (l_right: list (Spec.key * Spec.json_schema))
  (ih:
    (j': Spec.json_schema {j' << Spec.Object l}) ->
    (s': Spec.key {
      List.Tot.mem s' (List.Tot.map fst l) /\
      List.Tot.assoc s' l_left == Some j' /\
      Spec.object_as_type (Spec.Object l) as_type l s' == as_type j' /\
      Spec.object_as_type (Spec.Object l) Spec.as_gtype l s' == Spec.as_gtype j'
    }) ->
    Lemma
    (requires (forall_string_ptr1 j' (Struct.gfield ptr s') (DependentMap.sel data s') /\ forall_string_ptr2 j' (Struct.gfield ptr s') (DependentMap.sel data s')))
    (ensures (forall_string_ptrand j' (Struct.gfield ptr s') (DependentMap.sel data s')))
  )
: Lemma
  (requires (
     object_forall_string_ptr l forall_string_ptr1 ptr data l_left l_right /\
     object_forall_string_ptr l forall_string_ptr2 ptr data l_left l_right
  ))
  (ensures (object_forall_string_ptr l forall_string_ptrand ptr data l_left l_right))
= let h1: object_forall_string_ptr l forall_string_ptr1 ptr data l_left l_right = Squash.join_squash () in
  let h2: object_forall_string_ptr l forall_string_ptr2 ptr data l_left l_right = Squash.join_squash () in
  Squash.bind_squash h1 (fun o1 ->
    Squash.map_squash h2 (fun o2 ->
      object_forall_string_ptr_t_and l forall_string_ptr1 forall_string_ptr2 forall_string_ptrand ptr data l_left l_right o1 o2 ih
  ))

let forall_string_ptr_aux
  (p: string_ptr -> Spec.sstring -> GTot Type0)
  (j: Spec.json_schema)
  (g:  (j': Spec.json_schema {j' << j}) -> Struct.struct_ptr (as_type j') -> Spec.as_gtype j' -> GTot Type0)
  (ptr: Struct.struct_ptr (as_type j))
  (data: Spec.as_gtype j)
: GTot Type0
= match j with
  | Spec.String -> p ptr data
  | Spec.Object l ->
    object_forall_string_ptr l g ptr data l []

let rec forall_string_ptr
  (p: string_ptr -> Spec.sstring -> GTot Type0)
  (j: Spec.json_schema)
  (ptr: Struct.struct_ptr (as_type j))
  (data: Spec.as_gtype j)
: Ghost Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases j)
= forall_string_ptr_aux p j (let g
    (j': Spec.json_schema {j' << j})
    (ptr': Struct.struct_ptr (as_type j'))
    (data': Spec.as_gtype j')
    : GTot Type0
    = forall_string_ptr p j' ptr' data' in g) ptr data

let forall_string_ptr_object_eq
  (p: string_ptr -> Spec.sstring -> GTot Type0)
  (l:  list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)} )
  (ptr: Struct.struct_ptr (as_type (Spec.Object l)))
  (data: Spec.as_gtype (Spec.Object l))
: Lemma
  (ensures (forall_string_ptr p (Spec.Object l) ptr data == object_forall_string_ptr l (let g     (j': Spec.json_schema {j' << Spec.Object l})
      (ptr': Struct.struct_ptr (as_type j'))
(data': Spec.as_gtype j')
  = forall_string_ptr p j' ptr' data' in g) ptr data l []))
= assert_norm (forall_string_ptr p (Spec.Object l) ptr data == object_forall_string_ptr l (let g     (j': Spec.json_schema {j' << Spec.Object l})
    (ptr': Struct.struct_ptr (as_type j')) (data': Spec.as_gtype j')
 = forall_string_ptr p j' ptr' data' in g) ptr data l [])

let forall_string_ptr_object_equiv
  (p: string_ptr -> Spec.sstring -> GTot Type0)
  (l:  list (Spec.key * Spec.json_schema) {List.Tot.noRepeats (List.Tot.map fst l)} )
  (ptr: Struct.struct_ptr (as_type (Spec.Object l)))
  (data: Spec.as_gtype (Spec.Object l))
: Lemma
  (ensures (forall_string_ptr p (Spec.Object l) ptr data <==> object_forall_string_ptr l (forall_string_ptr p) ptr data l []))
= forall_string_ptr_object_eq p l ptr data;
  object_forall_string_ptr_equiv l (let g     (j': Spec.json_schema {j' << Spec.Object l})
  (ptr': Struct.struct_ptr (as_type j'))
    (data': Spec.as_gtype j')
 = forall_string_ptr p j' ptr' data' in g) (forall_string_ptr p) ptr data l []

let rec forall_string_ptr_implies
  (p1: (string_ptr -> Spec.sstring -> GTot Type0))
  (j: Spec.json_schema)
  (ptr: Struct.struct_ptr (as_type j))
  (data: Spec.as_gtype j)
  (p2: (string_ptr -> Spec.sstring -> GTot Type0) { forall (ptr': string_ptr { ptr `Struct.includes` ptr' }) b . p1  ptr' b ==> p2 ptr' b } )
: Lemma
  (requires (forall_string_ptr p1 j ptr data))
  (ensures (forall_string_ptr p2 j ptr data))
  (decreases j)  
= match j with
  | Spec.String -> ()
  | Spec.Object l ->
    forall_string_ptr_object_equiv p1 l ptr data;
    forall_string_ptr_object_equiv p2 l ptr data;
    let (ptr: Struct.struct_ptr (DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) as_type l))) = ptr in
    let (data: DependentMap.t (s: Spec.key {List.Tot.mem s (List.Tot.map fst l)}) (Spec.object_as_type (Spec.Object l) Spec.as_gtype l)) = data in
    object_forall_string_ptr_implies l (forall_string_ptr p1) (forall_string_ptr p2) ptr data l [] (fun j' s' ->
      let f (ptr': string_ptr { (Struct.gfield ptr s') `Struct.includes` ptr' }) : Lemma (forall b . p1  ptr' b ==> p2 ptr' b ) =
        Struct.includes_trans ptr (Struct.gfield ptr s') ptr'
      in
      let _ = Classical.forall_intro f in
      forall_string_ptr_implies p1 j' (Struct.gfield ptr s') (DependentMap.sel data s') p2
    )
