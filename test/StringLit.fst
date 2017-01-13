module StringLit

let main () =
  C.print_string (C.string_of_literal "hello, world\n");
  C.exit_success
