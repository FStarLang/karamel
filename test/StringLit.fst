module StringLit

module IO = FStar.HyperStack.IO

let test (x:string) = 
  FStar.String.strcat "hello " x
  
let main () =
  // C strings, modeled as zero-terminated, not relying on GC
  C.String.(print !$"hello, world\n");
  // F* strings, unaware of zero-termination, supports concatenation using a
  // conservative GC; HyperIO provides functions in the Stack effect
  IO.print_string (test "jonathan!\n");
  // Generates nice testcases to be run with clang -fsanitize=address...!
  IO.print_string (FStar.String.strcat "" "");
  IO.print_string (FStar.String.strcat "" "\n");
  IO.print_string (FStar.String.strcat "\n" "");
  C.exit_success
