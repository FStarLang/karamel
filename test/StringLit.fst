module StringLit
open FStar.String
let test (x:string) = 
  "hello " ^ x
  
let main () =
  C.print_string (C.string_of_literal "hello, world\n");
  // C.print_string (C.string_of_literal (test "jonathan!\n"));
  C.exit_success
