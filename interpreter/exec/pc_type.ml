open Svalues
open Z3
   
module Lets = Map.Make(struct
                  type t = int
                  let compare = compare
                end)
type rel_type = L of Expr.expr | H of Expr.expr * Expr.expr
                                    
type simpl = Z3Expr32 of rel_type | Z3Expr64 of rel_type | Sv of svalue
                                       
type pc_let = simpl Lets.t

let letnum = ref 0
           
type pc = PCTrue | PCFalse
          | PCAnd of svalue * pc
          (* | PCLet of svalue * svalue *)
          | PCExpr of rel_type
                    
type pc_ext = pc_let * pc

let svalue_to_string sv =
   match sv with
     | SI32 sv -> "Si32 " ^ Si32.to_string_s sv
     | SI64 sv -> "Si64 " ^ Si64.to_string_s sv
     | SF32 sv -> "F32 " ^ F32.to_string sv
     | SF64 sv -> "F64 " ^ F64.to_string sv

let svalue_depth sv n =
   match sv with
     | SI32 sv -> Si32.count_depth sv n
     | SI64 sv -> Si64.count_depth sv n
     | SF32 sv -> false
     | SF64 sv -> false

let svalue_newlet sv i =
   match sv with
   | Z3Expr32 _ -> SI32 (Si32.let_ i)
   | Z3Expr64 _ -> SI64 (Si32.let_ i)
   | Sv (SI32 sv) -> SI32 (Si32.let_ i)
   | Sv (SI64 sv) -> SI64 (Si64.let_ i)
   | Sv (SF32 sv) -> SF32 sv
   | Sv (SF64 sv) -> SF64 sv

(* function to check if assignment works *)
(* let svalue_eq sv tr =
 *    match sv,tr with
 *      | SI32 sv, SI32 tr -> SI32 (Si32.eq sv tr)
 *      | SI64 sv, SI64 tr -> SI64 (Si64.eq sv tr)
 *      | SF32 _, _ -> tr
 *      | SF64 _, _ -> tr
 *      | _ -> failwith "Not possible" *)

               
let rec print_pc pc =
  match pc with
  | PCTrue -> "True"
  | PCFalse -> "False"
  | PCAnd (sv, pc) -> "(" ^ svalue_to_string sv ^ ") " ^ "&" ^ " (" ^ print_pc pc ^ ")"
  | PCExpr (H (e1,e2)) -> "H (" ^ Expr.to_string e1 ^ ", " ^ Expr.to_string e2 ^ ")"
  | PCExpr (L e) -> "L (" ^ Expr.to_string e ^ ")"
                          
(* | PCLet (sv1, sv2) -> "let" ^ svalue_to_string sv1 ^ "=" ^ svalue_to_string sv2 *) 

let print_pc_let pcext =
  let pclet, pc = pcext in
  (* TODO(Romy): print the lets *)
  print_pc pc 

let next_let () =
  letnum := !letnum + 1;
  !letnum
  
let add_let (pce: pc_ext) (sv: simpl) =
  let pclet, pc = pce in
  let nl = next_let () in
  (* print_endline ("Add let:" ^ (string_of_int nl)); *)
  nl, (Lets.add nl sv pclet, pc)

let find_let (pce: pc_ext) (i: int) : simpl =
  let pclet, pc = pce in
  try
    Lets.find i pclet
  with Not_found ->
    failwith ("Not_found pc_let " ^ (string_of_int i)) 
        
  (* nl, (Lets.add nl sv pclet, pc) *)

let empty_pc () =
  (Lets.empty, PCTrue)

let pc_depth pc n =
  let rec pc_depth_i pc n acc = 
    match pc with
    | PCTrue | PCFalse | PCExpr _ -> (acc + 1 > n)
    | PCAnd (sv,pc) ->
       let d = svalue_depth sv (n - acc) in
       if d then true else 
         pc_depth_i pc (n - acc) (acc + 1)
    
  in
  pc_depth_i pc n 0
