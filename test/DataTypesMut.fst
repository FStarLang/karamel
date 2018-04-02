module DataTypesMut

module B = FStar.Buffer

noeq
type t1 a = a * a
and t2 a =
  | T2 of B.buffer (t3 a) * B.buffer (t3 Int32.t)
and t3 a =
  | T3 of a * t1 Int64.t * B.buffer (t2 a) * B.buffer (t2 Int16.t)

(* The dependency graph is as follows:

                 ,--------------.  ,--------.
                 |              |  v        |
                 |       -> t2 Int8.t -> t3 Int8.t  -----
                 |      /                   |            `
t2 Int8.t --> t3 Int8.t-.                  /             |
          \      |  |    --> t1 Int64.t <--              |
           \     v  |   /                  \             |
            -> t3 Int32.t -> t2 Int32.t     |            |
                 ^  \   \         |         |            |
                 |   -----> t2 Int16.t -> t3 Int16.t     |
                 |             |  | ^      |             |
                 `-------------'--'  `-----'-------------'

But! It is not KreMLin's problem to guarantee that the size of any of these
types is finite (it's the C compiler's). So, we just see type monomorphization
as a graph traversal; when we hit a loop, we just insert a forward type
declaration on-the-spot and remember to visit the type we needed later on.

Note: this only works if the graph is finite. F* (happily) accepts this program:

  module Test

  type t a = | C: t (a * a) -> t a | D

This sends KreMLin into a loop... we ought to detect this.
*)
type u1 = t2 Int8.t
type u2 = t2 UInt8.t
type u3 = t3 Int16.t

let main () = 0l
