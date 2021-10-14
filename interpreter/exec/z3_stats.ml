open Z3
  
type z3_stats_t = { num_numerals: int;
                    num_consts: int;
                    num_bvs: int;
                    num_adds: int;
                    num_divs: int;
                    num_muls: int;
                    num_logs: int;
                    num_other: int;
                    num_comps: int;
                    num_exts: int;
                    num_shifts: int;

                    num_bool: int;
                    num_bool_eqs   : int;
                    num_bool_nots  : int;
                    num_bool_ites  : int;
                    num_bool_falses: int;
                    num_bool_trues : int;
                    num_bool_ands  : int;
                    num_bool_ors   : int;
                    num_bool_other : int;

                    num_array        : int;
                    num_array_store  : int;
                    num_array_select : int;
                    num_array_other : int;
                  }


let print_stats stats =
  print_endline "Printing Z3 stats";
  print_endline (string_of_int stats.num_numerals);
  print_endline (string_of_int stats.num_consts)


let z3stats_to_string stats =
  (string_of_int stats.num_consts)
  (* array *)
  ^ ":" ^ (string_of_int stats.num_array)
  ^ ":" ^ (string_of_int stats.num_array_store)
  ^ ":" ^ (string_of_int stats.num_array_select)
  ^ ":" ^ (string_of_int stats.num_array_other)
  (* BitVectors *)
  ^ ":" ^ (string_of_int stats.num_bvs)
  ^ ":" ^ (string_of_int stats.num_adds)
  ^ ":" ^ (string_of_int stats.num_muls)
  ^ ":" ^ (string_of_int stats.num_divs)
  ^ ":" ^ (string_of_int stats.num_comps)
  ^ ":" ^ (string_of_int stats.num_logs)
  ^ ":" ^ (string_of_int stats.num_shifts)
  ^ ":" ^ (string_of_int stats.num_numerals)
  ^ ":" ^ (string_of_int stats.num_exts)
  ^ ":" ^ (string_of_int stats.num_other) 
  (* bools *)
  ^ ":" ^ (string_of_int stats.num_bool)
  ^ ":" ^ (string_of_int stats.num_bool_ites)
  ^ ":" ^ (string_of_int stats.num_bool_eqs)
  ^ ":" ^ (string_of_int stats.num_bool_nots)
  ^ ":" ^ (string_of_int stats.num_bool_trues)
  ^ ":" ^ (string_of_int stats.num_bool_falses)
  ^ ":" ^ (string_of_int stats.num_bool_ands)
  ^ ":" ^ (string_of_int stats.num_bool_ors)
  ^ ":" ^ (string_of_int stats.num_bool_other) 

          
let inc_numerals stats =
  {stats with num_numerals = stats.num_numerals + 1}

let inc_consts stats =
  {stats with num_consts = stats.num_consts + 1}

let inc_bvs stats =
  {stats with num_bvs = stats.num_bvs + 1}

let inc_adds stats =
  {stats with num_adds = stats.num_adds + 1}

let inc_muls stats =
  {stats with num_muls = stats.num_muls + 1}

let inc_logs stats =
  {stats with num_logs = stats.num_logs + 1}

let inc_shifts stats =
  {stats with num_shifts = stats.num_shifts + 1}

  
let inc_divs stats =
  {stats with num_divs = stats.num_divs + 1}

let inc_comps stats =
  {stats with num_comps = stats.num_comps + 1}

let inc_other stats =
  {stats with num_other = stats.num_other + 1}

let inc_exts stats =
  {stats with num_exts = stats.num_exts + 1}

(* Arrays *)  
let inc_array stats =
  {stats with num_array = stats.num_array + 1}

let inc_array_select stats =
  {stats with num_array_select = stats.num_array_select + 1}

let inc_array_store stats =
  {stats with num_array_store = stats.num_array_store + 1}

let inc_array_other stats =
  {stats with num_array_other = stats.num_array_other + 1}

  
(* Bools *)
let inc_bool stats =
  {stats with num_bool = stats.num_bool + 1}

let inc_bool_ands stats =
  {stats with num_bool_ands = stats.num_bool_ands + 1}

let inc_bool_ors stats =
  {stats with num_bool_ors = stats.num_bool_ors + 1}

let inc_bool_trues stats =
  {stats with num_bool_trues = stats.num_bool_trues + 1}

let inc_bool_falses stats =
  {stats with num_bool_falses = stats.num_bool_falses + 1}

let inc_bool_nots stats =
  {stats with num_bool_nots = stats.num_bool_nots + 1}

let inc_bool_ites stats =
  {stats with num_bool_ites = stats.num_bool_ites + 1}

let inc_bool_eqs stats =
  {stats with num_bool_eqs = stats.num_bool_eqs + 1}

let inc_bool_other stats =
  {stats with num_bool_other = stats.num_bool_other + 1}

let empty_stats () =
  { num_numerals = 0;
    num_consts = 0;
    num_bvs = 0;
    num_adds = 0;
    num_muls = 0;
    num_logs = 0;
    num_divs = 0;
    num_comps = 0;
    num_shifts = 0;
    num_exts = 0;
    num_other = 0;
    (* Arrays *)
    num_array = 0;
    num_array_store = 0;
    num_array_select = 0;
    num_array_other = 0;
    (* Bools *)
    num_bool = 0;
    num_bool_eqs = 0;
    num_bool_nots = 0;
    num_bool_ites = 0;
    num_bool_falses = 0;
    num_bool_trues = 0;
    num_bool_ands = 0;
    num_bool_ors = 0;
    num_bool_other = 0;
  }
  
  
   
let rec get_stats_exps (exps: Z3.Expr.expr list) (stats: z3_stats_t) : z3_stats_t =
  match exps with
  | [] -> stats
  | exp::exps' ->
     let stats' = get_stats_exp exp stats in
     get_stats_exps exps' stats'

     
and get_stats_exp (exp: Z3.Expr.expr) (stats: z3_stats_t) : z3_stats_t =
  let sort = Expr.get_sort exp in

  let stats' = 
    (match Sort.get_sort_kind sort with
     | Z3enums.BOOL_SORT ->
        (try
           if Boolean.is_false exp then
             inc_bool_falses stats |> inc_bool
           else if Boolean.is_true exp then
             inc_bool_trues stats |> inc_bool
           else if Boolean.is_eq exp then
             inc_bool_eqs stats |> inc_bool
           else if Boolean.is_ite exp then
             inc_bool_ites stats |> inc_bool
           else if Boolean.is_and exp then
             inc_bool_ands stats |> inc_bool
           else if Boolean.is_or exp then
             inc_bool_ors stats |> inc_bool
           else if Boolean.is_not exp then
             inc_bool_nots stats |> inc_bool
           else
             inc_bool_other stats |> inc_bool
         with _ ->               
           inc_bool stats)
     | Z3enums.BV_SORT ->
        (try
           if BitVector.is_bv_add exp || BitVector.is_bv_sub exp then
             inc_adds stats |> inc_bvs
           else if BitVector.is_bv_mul exp then
             inc_muls stats |> inc_bvs
           else if BitVector.is_bv_numeral exp then
             inc_numerals stats |> inc_bvs
           else if BitVector.is_bv_sdiv exp
                   || BitVector.is_bv_udiv exp 
                   || BitVector.is_bv_urem exp 
                   || BitVector.is_bv_SRem exp then
             inc_divs stats |> inc_bvs
           else if BitVector.is_bv_ule exp
                   || BitVector.is_bv_sle exp 
                   || BitVector.is_bv_uge exp 
                   || BitVector.is_bv_sge exp
                   || BitVector.is_bv_ult exp
                   || BitVector.is_bv_slt exp 
                   || BitVector.is_bv_ugt exp 
                   || BitVector.is_bv_sgt exp then
             inc_comps stats |> inc_bvs
           else if BitVector.is_bv_and exp
                   || BitVector.is_bv_or exp 
                   || BitVector.is_bv_not exp 
                   || BitVector.is_bv_xor exp
                   || BitVector.is_bv_nand exp
                   || BitVector.is_bv_nor exp 
                   || BitVector.is_bv_xnor exp then
             inc_logs stats |> inc_bvs
           else if BitVector.is_bv_shiftleft exp
                   || BitVector.is_bv_shiftrightlogical exp 
                   || BitVector.is_bv_shiftrightarithmetic exp 
                   || BitVector.is_bv_rotateleft exp
                   || BitVector.is_bv_rotateright exp then
             inc_shifts stats |> inc_bvs            
           else if BitVector.is_bv_signextension exp
                   || BitVector.is_bv_zeroextension exp 
                   || BitVector.is_bv_extract exp 
                   || BitVector.is_bv_concat exp  then
             inc_exts stats |> inc_bvs            
           else
             inc_other stats |> inc_bvs 
         with _ ->
           inc_bvs stats)
     | Z3enums.ARRAY_SORT ->
        (try
           if Z3Array.is_store exp then
             inc_array_store stats |> inc_array
           else if Z3Array.is_select exp then
             inc_array_select stats |> inc_array
            else
              inc_array_other stats |> inc_array
         with _ ->               
           inc_array stats)
     | _ -> stats
    )
  in
  
  (* let sort_str = Sort.to_string sort in *)
  (* print_endline ("Sort: " ^ sort_str); *)

  (* let num_args = Expr.get_num_args exp in *)
  (* print_endline ("Num args: " ^ string_of_int num_args); *)
  let stats'' = 
    (* if (Expr.is_numeral exp) then
     *   inc_numerals stats'
     * else *)
    if (Expr.is_const exp) then
      inc_consts stats'
    else stats'
  in

  let args = Expr.get_args exp in
  get_stats_exps args stats''


let get_stats_z3exp (exps: Z3.Expr.expr list) : z3_stats_t  =
  let nstats = empty_stats() in
  get_stats_exps exps nstats 




let all_features_to_array num_exprs intqtype exprs =
  let stats = get_stats_z3exp exprs in
  [|[| intqtype;
       num_exprs;
       stats.num_consts;
       stats.num_array;
       stats.num_array_store;
       stats.num_array_select;
       stats.num_array_other;
       stats.num_bvs;
       stats.num_adds;
       stats.num_muls;
       stats.num_divs;
       stats.num_comps;
       stats.num_logs;
       stats.num_shifts;
       stats.num_numerals;
       stats.num_exts;
       stats.num_other;
       stats.num_bool;
       stats.num_bool_ites;
       stats.num_bool_eqs;
       stats.num_bool_nots;
       stats.num_bool_trues;
       stats.num_bool_falses;
       stats.num_bool_ands;
       stats.num_bool_ors;
       stats.num_bool_other |] |]
