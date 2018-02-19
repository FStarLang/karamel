module MallocFree

open FStar.HyperStack.ST

let main (): St C.exit_code =
  let x = Buffer.rcreate_mm FStar.HyperStack.root 42ul 1ul in
  TestLib.checku32 (Buffer.index x 0ul) 42ul;
  Buffer.rfree x;
  C.EXIT_SUCCESS
