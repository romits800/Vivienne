open Svalues

type pc = PCTrue | PCFalse
          | PCAnd of svalue * pc


let svalue_to_string sv =
   match sv with
     | SI32 sv -> Si32.to_string_s sv
     | SI64 sv -> Si64.to_string_s sv
     | SF32 sv -> F32.to_string sv
     | SF64 sv -> F64.to_string sv
  
let rec print_pc pc =
  match pc with
  | PCTrue -> "True"
  | PCFalse -> "False"
  | PCAnd (sv, pc) -> "(" ^ svalue_to_string sv ^ ") " ^ "&" ^ " (" ^ print_pc pc ^ ")"
