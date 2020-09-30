open Svalues

type pc = PCTrue | PCFalse
          | PCAnd of svalue * pc
          (* | PCEqZ of svalue
           * | PCNeqZ of svalue *)


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
  (* | PCEqZ sv -> "(" ^ svalue_to_string sv ^ " = 0"
   * | PCNeqZ sv -> "(" ^ svalue_to_string sv ^ " != 0" *)
  | PCAnd (sv, pc) -> "(" ^ svalue_to_string sv ^ ") " ^ "&" ^ " (" ^ print_pc pc ^ ")"
