module UnusedParameterUnknown

open FStar.HyperStack.ST

// Leave the callee undeclared in Karamel's input, as with a macro emitted by
// an extraction plugin. Its argument types are therefore unknown to Karamel.
noextract
let external_identity (x: Int32.t): St Int32.t = x

[@ (CPrologue "#define external_identity(x) (x)") ] // a bit of a hack to insert a macro
let forward (x: Int32.t): St Int32.t =
  // Removing unused parameters must preserve this use of x, even though the
  // callee has no known parameter types. Previously this raised Failure("nth").
  external_identity x

let main (): St Int32.t =
  if forward 42l = 42l then 0l else 1l
