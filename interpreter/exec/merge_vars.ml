open Eval
(*open Pc_type*)
open Source
   
module LoopVarMap = Map.Make(struct
                   type t = string
                   let compare = compare
                 end)


let get_policy_loopvar = function
  | LocalVar (x,is_low,mo) -> is_low
  | GlobalVar (x,is_low,mo) -> is_low
  | StoreVar (sv, ty, sz, is_low, mo) -> is_low
    
let is_int_addr sv =
    match sv with
    | Svalues.SI32 s32 -> Si32.is_int s32
    | _ -> failwith "Address should be i32."

let get_int_addr sv =
    match sv with
    | Svalues.SI32 s32 -> Si32.to_int_u s32
    | _ -> failwith "Address should be i32."

(* Merge new variables *)
let  merge_vars (lv: loopvar_t list) : loopvar_t list =
  let rec merge_vars_i (lv: loopvar_t list)
            (mp: (loopvar_t * int)  LoopVarMap.t) : loopvar_t list =
    match lv with
    | (LocalVar (x,is_low,mo) as lvh) :: lvs ->
       let str = "Local" ^ string_of_int (Int32.to_int x.it) in 
       (try
          let is_low_old = LoopVarMap.find str mp |> fst |> get_policy_loopvar in
          if (is_low_old = is_low) then
              merge_vars_i lvs mp
          else (
              let mp' = LoopVarMap.add str (LocalVar (x,false,mo), 2) mp in
              merge_vars_i lvs mp'
          )
        with Not_found ->
          let mp' = LoopVarMap.add str (lvh,2) mp in
          merge_vars_i lvs mp'
       )
    | (GlobalVar (x,is_low,mo) as lvh) :: lvs ->
       let str = "Global" ^ string_of_int (Int32.to_int x.it) in
       (try
          let is_low_old = LoopVarMap.find str mp |> fst |> get_policy_loopvar in
          if (is_low_old = is_low) then 
              merge_vars_i lvs  mp
          else (
              let mp' = LoopVarMap.add str (GlobalVar (x,false,mo), 2) mp in
              merge_vars_i lvs  mp'
          )
        with Not_found ->
          let mp' = LoopVarMap.add str (lvh, 2) mp in
          merge_vars_i lvs mp'
       )

    (* merge store only when they happen in consecutive loops - 
       otherwise the local/global variables take care of it
       take care of it *)
    (*| _ :: lvs -> merge_vars_i lvs mp*)
    | (StoreVar (sv, ty, sz, is_low, mo) as lvh) :: lvs ->
       if (!Flags.debug) then
         print_loopvar lvh;
       (* Todo(Romy) add a flag for this *)
       if (!Flags.exclude_zero_address && is_int_addr sv && get_int_addr sv = 0) then (
         if !Flags.debug then print_endline "Address is zero";
         merge_vars_i lvs mp
       ) else (
         
         let str = "Store" ^ Pc_type.svalue_to_string sv in
         (try
            let lh, num = LoopVarMap.find str mp in
            let is_low_old = lh |> get_policy_loopvar in
            if (is_low_old = is_low) then (
              (* Increase number of times we found this *)
              let mp' = LoopVarMap.add str (lvh, num+1) mp in
              merge_vars_i lvs mp'
            )
            else (
              let mp' = LoopVarMap.add str (StoreVar (sv, ty, sz, false, mo), num+1) mp in
              merge_vars_i lvs mp'
            )
          with Not_found ->
            let mp' = LoopVarMap.add str (lvh, 1) mp in
            (* merge_vars_i lvs (lvh::acc) mp' *)
            merge_vars_i lvs mp'
         )
       )

    | [] -> LoopVarMap.bindings mp |>
              List.filter (fun (k,(v,num)) -> num > 1) |>
              List.map (fun (k,(v,num)) -> v) 
         
  in
  if (!Flags.debug) then 
      print_endline "Merging variables";
  let mp = LoopVarMap.empty in
  merge_vars_i lv mp
