

%token LPAREN RPAREN EQUALS
%token <string>VAR

%token<string> BINARY
%token EOF
/*%token AS
%token CONST*/
/*%token MODEL*/
/*%token ARRAY*/
/*%token DEFINE_FUN
%token UNDERSCORE
%token <int>NUM*/
/*%token INT*/
/* %token SAT
 * %token UNSAT */

%start model             /* the entry point */
%type <Smtlib.yices_model> model
%%

model:
 definitions EOF { print_endline "sat"; Smtlib.Sat $1 }
;

definitions:
 | /*empty*/       { [] }
 | definition definitions { $1::$2 }
;

definition:
  LPAREN EQUALS VAR BINARY RPAREN { ($3,$4)  }
;

