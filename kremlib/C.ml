open FStar_Buffer

type exit_code =
  | EXIT_SUCCESS
  | EXIT_FAILURE

let exit_success = 0
let exit_failure = 255

let string_of_literal s = s
let print_string = print_string
