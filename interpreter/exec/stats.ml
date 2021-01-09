(* Solver statistics *)
type stat_t = { z3 : int; cvc4 : int; boolector : int; yices : int} 

let stats = ref { z3 = 0; cvc4 = 0; boolector = 0; yices = 0 }


let print_stats () =
  print_endline @@ "Z3 : " ^ (string_of_int !stats.z3);
  print_endline @@ "Yices : " ^ (string_of_int !stats.yices);
  print_endline @@ "Boolector : " ^ (string_of_int !stats.boolector);
  print_endline @@ "CVC4 : " ^ (string_of_int !stats.cvc4);
