%{
  open Bundle
%}

%token<int>     INT
%token<string>  UIDENT
%token          PLUS MINUS STAR AT DOT EOF COMMA EQUALS

%start <(Flags.flag * (int * int)) list> warn_error_list
%start <Bundle.t> bundle
%start <Bundle.pat> pat

(** Parsing of command-line error/warning/silent flags. *)

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


(** Parsing of -bundle options *)

pat:
| u = UIDENT DOT STAR
  { Prefix [ u ] }
| u = UIDENT
  { Module [ u ] }
| u = UIDENT DOT p = pat
  { match p with
    | Module m ->
        Module (u :: m)
    | Prefix m ->
        Prefix (u :: m) }

bundle:
| b = separated_list(DOT, u = UIDENT { u }) EQUALS l = separated_nonempty_list(COMMA, pat) EOF
  { b, l }
