open Z3_stats
(* Solver statistics *)

(* q_type:       is_sat queries - from branches
 *               is_v_ct_sat queries - for check branches and loads/stores
 *               are_same - check if values are same - invariant
 *               find_solutions - find the solutions for call_indirect 
 *               is_ct_unsat - not in use - indirect leakages *)
type q_type = IS_SAT | IS_V_CT_SAT | ARE_SAME | SOLUTION | IS_CT_UNSAT

type query_t = { solver: string; num_exprs: int; time: float;
                 query_type: q_type; 
                 expr_stats: z3_stats_t}

type stat_t = { z3 : int; cvc4 : int; boolector : int;
                bitwuzla : int; yices : int; queries : query_t list} 

let stats = ref { z3 = 0; cvc4 = 0; boolector = 0; yices = 0; bitwuzla = 0;
                  queries = []}
          
let init_stats () =
  stats := { z3 = 0; cvc4 = 0;
             boolector = 0; yices = 0;
             bitwuzla = 0; queries = [] }

let update_stats = function
  | "cvc4"  ->  stats := {!stats with cvc4 = !stats.cvc4 + 1 }
  | "yices" ->  stats := {!stats with yices = !stats.yices + 1 }
  | "z3"    ->  stats := {!stats with z3 = !stats.z3 + 1 }
  | "boolector" -> stats := {!stats with bitwuzla = !stats.boolector + 1 }
  | "bitwuzla" -> stats := {!stats with bitwuzla = !stats.bitwuzla + 1 }
  | _ -> failwith "Unknown solver"

  

let string_of_qtype = function
    | IS_SAT      -> "0"
    | IS_V_CT_SAT -> "1"
    | ARE_SAME    -> "2"
    | SOLUTION    -> "3"
    | IS_CT_UNSAT -> "4"

let print_query q =
  print_endline @@ q.solver ^ ":" ^ string_of_qtype q.query_type ^ ":" ^  string_of_int q.num_exprs 
                   ^ ":" ^ z3stats_to_string q.expr_stats ^ ":" ^ string_of_float q.time


let solver_small_to_capital = function
  | "cvc4" -> "CVC4"
  | "yices" -> "Yices"
  | "z3" -> "Z3"
  | "boolector" -> "Boolector"
  | "bitwuzla" -> "BitWuzla"
  | _ -> failwith "Unknown solver"
                 
let print_stats () =
  print_endline @@ "Z3 : " ^ (string_of_int !stats.z3);
  print_endline @@ "Yices : " ^ (string_of_int !stats.yices);
  print_endline @@ "Boolector : " ^ (string_of_int !stats.boolector);
  print_endline @@ "CVC4 : " ^ (string_of_int !stats.cvc4);
  print_endline @@ "Bitwuzla : " ^ (string_of_int !stats.bitwuzla);
  List.iter print_query !stats.queries

let add_new_query sol num_exprs exprs qtyp t =
  stats := {!stats with queries = ({solver = sol;
                                    num_exprs = num_exprs;
                                    time = t;
                                    query_type = qtyp;
                                    expr_stats = get_stats_z3exp exprs}::!stats.queries)}


let update_query_str sol =
  match !stats.queries with
  | s::t -> stats := {!stats with queries = {s with solver = sol}::t}
  | [] -> failwith "No query"


let update_query_time t =
  match !stats.queries with
  | s::tail -> stats := {!stats with queries = {s with time = t}::tail}
  | [] -> failwith "No query"


let print_last () =
  print_query (List.hd !stats.queries)
