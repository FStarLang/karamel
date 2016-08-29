%token<int>     INT
%token          PLUS MINUS AT DOT EOF

%start <(Flags.flag * (int * int)) list> warn_error_list

(* Parsing of command-line error/warning/silent flags. *)

%%

warn_error_list:
| ws = warn_error+ EOF
  { ws }

warn_error:
| f = flag r = range
  { f, r }

flag:
| AT
  { Flags.CError }
| MINUS
  { Flags.CSilent }
| PLUS
  { Flags.CWarning }

range:
| i = INT
  { i, i }
| i = INT DOT DOT j = INT
  { i, j }

