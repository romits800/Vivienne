open Svalues

type pc = PCTrue | PCFalse
          | PCAnd of svalue * pc
          (* | PCLet of svalue * svalue *)


let svalue_to_string sv =
   match sv with
     | SI32 sv -> Si32.to_string_s sv
     | SI64 sv -> Si64.to_string_s sv
     | SF32 sv -> F32.to_string sv
     | SF64 sv -> F64.to_string sv

let svalue_depth sv =
   match sv with
     | SI32 sv -> Si32.count_depth sv
     | SI64 sv -> Si64.count_depth sv
     | SF32 sv -> 1
     | SF64 sv -> 1

let svalue_newhigh sv =
   match sv with
     | SI32 sv -> SI32 (Si32.of_high ())
     | SI64 sv -> SI64 (Si64.of_high ())
     | SF32 _ -> sv
     | SF64 _ -> sv

(* function to check if assignment works *)
let svalue_eq sv tr =
   match sv,tr with
     | SI32 sv, SI32 tr -> SI32 (Si32.eq sv tr)
     | SI64 sv, SI64 tr -> SI64 (Si64.eq sv tr)
     | SF32 _, _ -> tr
     | SF64 _, _ -> tr
     | _ -> failwith "Not possible"

               
let rec print_pc pc =
  match pc with
  | PCTrue -> "True"
  | PCFalse -> "False"
  | PCAnd (sv, pc) -> "(" ^ svalue_to_string sv ^ ") " ^ "&" ^ " (" ^ print_pc pc ^ ")"
  (* | PCLet (sv1, sv2) -> "let" ^ svalue_to_string sv1 ^ "=" ^ svalue_to_string sv2 *) 
