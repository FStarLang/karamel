module StringLit

let test (x:string) = 
  FStar.String.strcat "hello " x
  
let main () =
  C.print_string (C.string_of_literal "hello, world\n");
  // C.print_string (C.string_of_literal (test "jonathan!\n"));
  C.exit_success
