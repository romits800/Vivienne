open Eval
(*open Pc_type*)
open Source
   
module LoopVarMap = Map.Make(struct
                   type t = string
                   let compare = compare
                 end)


let get_policy_loopvar = function
  | LocalVar (x, is_low, mo, v) -> is_low
  | GlobalVar (x, is_low, mo, v) -> is_low
  | StoreVar (sv, ty, sz, is_low, mo, loc) -> is_low
  | StoreZeroVar (_) -> true

let get_value_loopvar = function
  | LocalVar (x, is_low, mo, v) -> v
  | GlobalVar (x, is_low, mo, v) -> v
  | _ -> None

(* Merge new variables *)
let merge_vars (lv: loopvar_t list) (lv_stats: loopvar_t list) : loopvar_t list =
  let remove_values = function
    | _, (LocalVar (x,is_low,mo,v), 1) -> LocalVar(x, is_low, mo, None)
    | _, (GlobalVar (x,is_low,mo,v), 1) -> GlobalVar(x, is_low, mo, None)
    | _, (LocalVar (x,is_low,mo,v), _) -> LocalVar(x, is_low, mo, v)
    | _, (GlobalVar (x,is_low,mo,v), _) -> GlobalVar(x, is_low, mo, v)
    | _, (v, _) -> v
  in

  let rec merge_vars_i (lv: loopvar_t list)
            (mp: (loopvar_t * int)  LoopVarMap.t) : (loopvar_t * int)  LoopVarMap.t = 
    match lv with
    | (LocalVar (x,is_low,mo,v) as lvh) :: lvs ->
       let str = "Local" ^ string_of_int (Int32.to_int x.it) in 
       (try
          let old_val, num = LoopVarMap.find str mp  in
          let is_low_old = old_val |> get_policy_loopvar in
          let new_is_low = if is_low_old = is_low then is_low else false in

          (match old_val |> get_value_loopvar,v with
           | Some (sv1,simp1), Some (sv2,simp2) when simpl_equal simp1 simp2 ->

                let mp' = LoopVarMap.add str (LocalVar (x,new_is_low,mo,Some (sv1,simp1)), num + 1) mp in
                merge_vars_i lvs mp'
           | _,_ ->
                let mp' = LoopVarMap.add str (LocalVar (x,new_is_low,mo,None), num+1) mp in
(* >>>>>>> 84fe834dc26dbfc0ee2bf01952c9afd9b3aea50e *)
                merge_vars_i lvs mp'
          )
        with Not_found ->
          let mp' = LoopVarMap.add str (lvh,1) mp in
          merge_vars_i lvs mp'
       )
    | (GlobalVar (x,is_low,mo,v) as lvh) :: lvs ->
       let str = "Global" ^ string_of_int (Int32.to_int x.it) in
       (try
          let old_val, num = LoopVarMap.find str mp in
          let is_low_old = old_val |> get_policy_loopvar in
          let new_is_low = if is_low_old = is_low then is_low else false in

          (match old_val |> get_value_loopvar,v with

           | Some (sv1,simp1), Some (sv2,simp2)  when simpl_equal simp1 simp2  ->

              let mp' = LoopVarMap.add str (GlobalVar (x,new_is_low,mo,Some (sv1,simp1)), num+1) mp in
              merge_vars_i lvs mp'
           | _,_ ->
              let mp' = LoopVarMap.add str (GlobalVar (x,new_is_low,mo,None), num+1) mp in
              merge_vars_i lvs mp'
          )

        with Not_found ->
          let mp' = LoopVarMap.add str (lvh, 1) mp in
          merge_vars_i lvs mp'
       )

    (* merge store only when they happen in consecutive loops - 
       otherwise the local/global variables take care of it
       take care of it *)
    | (StoreVar (Some sv, ty, sz, is_low, mo, loc) as lvh) :: lvs ->
       (* Todo(Romy) add a flag for this *)
       if (!Flags.exclude_zero_address && is_int_addr sv && get_int_addr sv = 0) then (
         if !Flags.debug then print_endline "Address is zero";
         merge_vars_i lvs mp
       ) else (
         
         let str = "Store" ^ string_of_region loc in
         (try
            let lh, num = LoopVarMap.find str mp in
            let is_low_old = lh |> get_policy_loopvar in
            if (is_low_old = is_low) then (
              (* Increase number of times we found this *)
              let mp' = LoopVarMap.add str (lvh, num+1) mp in
              merge_vars_i lvs mp'
            )
            else (
              let mp' = LoopVarMap.add str (StoreVar (Some sv, ty, sz, false, mo, loc), num+1) mp in
              merge_vars_i lvs mp'
            )
          with Not_found ->
            let mp' = LoopVarMap.add str (lvh, 1) mp in
            (* merge_vars_i lvs (lvh::acc) mp' *)
            merge_vars_i lvs mp'
         )
       ) 
    | StoreVar _ :: lvs ->
       failwith "Not expected StoreZeroVar in merge_variables."
    | (StoreZeroVar (sv)) :: lvs ->
       failwith "Not expected StoreZeroVar in merge_variables."
    | [] -> mp
  in

  let rec merge_stats_vars_i (lv: loopvar_t list)
            (mp: (loopvar_t * int)  LoopVarMap.t) : loopvar_t list =
    match lv with
    | (LocalVar (x,is_low,mo,v) as lvh) :: lvs ->
       let str = "Local" ^ string_of_int (Int32.to_int x.it) in 
       (try
          let _ = LoopVarMap.find str mp in
          merge_stats_vars_i lvs mp
        with Not_found ->
          let mp' = LoopVarMap.add str (lvh,1) mp in
          merge_stats_vars_i lvs mp'
       )
    | (GlobalVar (x,is_low,mo,v) as lvh) :: lvs ->
       let str = "Global" ^ string_of_int (Int32.to_int x.it) in
       (try
          let _ = LoopVarMap.find str mp in
          merge_stats_vars_i lvs mp
        with Not_found ->
          let mp' = LoopVarMap.add str (lvh, 1) mp in
          merge_stats_vars_i lvs mp'
       )
    | (StoreVar (_, ty, sz, is_low, mo, loc) as lvh) :: lvs ->
       (* if (!Flags.exclude_zero_address && is_int_addr sv && get_int_addr sv = 0) then (
        *   if !Flags.debug then print_endline "Address is zero";
        *   merge_stats_vars_i lvs mp
        * ) else ( *)
       
       let str = "Store" ^ string_of_region loc in
       (try
          let _ = LoopVarMap.find str mp in
          merge_stats_vars_i lvs mp
        with Not_found ->
          let mp' = LoopVarMap.add str (lvh, 1) mp in
          merge_stats_vars_i lvs mp'
       )
    (* ) *)
    | (StoreZeroVar (sv)) :: lvs ->
       failwith "Not expected StoreZeroVar in merge_variables."
    | [] -> LoopVarMap.bindings mp |>
              (*List.filter (fun (k,(v,num)) -> num > 1) |>*)
              List.map remove_values
              (*List.map (fun (k,(v,num)) -> v) *)
          
  in
  if (!Flags.debug) then 
    print_endline "Merging variables";
  let mp = LoopVarMap.empty in
  let mp' = merge_vars_i lv mp in
  merge_stats_vars_i lv_stats mp'



let add_store_zero c lvs =
  let ty = Types.I32Type in 
  let final_addr = Svalues.SI32 (Si32.of_int_u 0) in
  let nv = Eval_symbolic.eval_load ty final_addr 
             (smemlen c.frame.inst) (smemnum c.frame.inst) 4 None
  in
  (StoreZeroVar nv):: lvs



