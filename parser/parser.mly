%{
  open Bundle
%}

%token<int>     INT
%token<string>  UIDENT
%token          PLUS MINUS STAR AT DOT EOF COMMA EQUALS PUBLIC LPAREN RPAREN

%start <(Flags.flag * (int * int)) list> warn_error_list
%start <Bundle.t> bundle
%start <Bundle.pat list> drop

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
| STAR
  { Prefix [ ] }
| u = UIDENT
  { Module [ u ] }
| u = UIDENT DOT p = pat
  { match p with
    | Module m ->
        Module (u :: m)
    | Prefix m ->
        Prefix (u :: m) }

mident:
| l = separated_list(DOT, u = UIDENT { u })
{ l }

api:
| m = mident
  { m }
| PUBLIC LPAREN m = mident RPAREN
  { m }

drop:
| p = separated_list(COMMA, pat) EOF
  { p }

bundle:
| apis = separated_nonempty_list(PLUS, api) 
  EQUALS
  l = separated_nonempty_list(COMMA, pat) EOF
  { apis, l }
| l = separated_nonempty_list(COMMA, pat) EOF
  { [], l }
