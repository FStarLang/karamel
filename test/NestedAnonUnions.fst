module NestedAnonUnions

module HST = FStar.HyperStack.ST

// The code generated for A1 true used a val field even when using anonymous unions.
// $ ./krml Bug.fst -skip-linking
// ✘ [CC,oo/Bug.c] (use -verbose to see the output)
// oo/Bug.c: In function ‘Bug_dummy’:
// oo/Bug.c:45:62: error: ‘Bug_t1’ {aka ‘struct Bug_t1_s’} has no member named ‘val’
//    45 |     ((Bug_t2){ .tag = Bug_A2, { .case_A2 = { .tag = Bug_A1, .val = { .case_A1 = true } } } });
//       |                                                              ^~~

noeq type t1 = | A1 of bool | B1 of bool
noeq type t2 = | A2 of t1 | B2 of bool

let dummy () : t2 =
  A2 (A1 true)

let dummy2 () : t2 =
  [@@CInline]
  let zero: t1 = A1 true in
  A2 zero

let main () : HST.St Int32.t =
  0l
