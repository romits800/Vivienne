{
  open Smt2_parser        (* The type token is defined in parser.mli *)
}
let lower = ['a'-'z''_']
let upper = ['A'-'Z''_']
let digit = ['0'-'9']
(* let other = ['~' '!' '@' '$' '%' '^' '&' '*'
 *                  '_' '-' '+' '=' '<' '>' '.' '?' '/''|'
 *             ] *)
let startchar= (lower | upper)

  rule token = parse
    [' ' '\t' '\n']     { token lexbuf }     (* skip blanks *)
  (* | ['\n' ]        { EOL } *)
  (* | ['0'-'9']+     { NUM(int_of_string(Lexing.lexeme lexbuf)) } *)
  | "#b" (['0'-'1']+ as s)  { BINARY(s) }

  (* | "unsat"        { UNSAT } *)
  (* | "Int"          { INT } *)
  (* | "BitVec"       { BV } *)
  (* | "sat"          { SAT } *)
  (* | "model"        { MODEL }
   * | "array"        { ARRAY }
   * | "const"        { CONST }
   * | "as"           { AS } *)
  | startchar (startchar | digit)* {
      let s = Lexing.lexeme lexbuf in
      VAR s
    }
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | '='            { EQUALS }
  | eof            { EOF }
