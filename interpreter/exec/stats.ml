(* Solver statistics *)

type query_t = { solver: string; num_exprs: int; time: float }
type stat_t = { z3 : int; cvc4 : int; boolector : int;
                bitwuzla : int; yices : int; queries : query_t list} 

let stats = ref { z3 = 0; cvc4 = 0; boolector = 0; yices = 0; bitwuzla = 0;
                  queries = [] }

let init_stats () =
  stats := { z3 = 0; cvc4 = 0;
             boolector = 0; yices = 0;
             bitwuzla = 0; queries = [] }

let print_query q =
  print_endline (q.solver ^ ": " ^ string_of_int q.num_exprs ^ ": " ^ string_of_float q.time)
  
let print_stats () =
  print_endline @@ "Z3 : " ^ (string_of_int !stats.z3);
  print_endline @@ "Yices : " ^ (string_of_int !stats.yices);
  print_endline @@ "Boolector : " ^ (string_of_int !stats.boolector);
  print_endline @@ "CVC4 : " ^ (string_of_int !stats.cvc4);
  print_endline @@ "Bitwuzla : " ^ (string_of_int !stats.bitwuzla);
  List.iter print_query !stats.queries

let add_new_query sol num_exprs t =
  stats := {!stats with queries = ({solver = sol;
                                    num_exprs = num_exprs;
                                    time = t}::!stats.queries)}


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
