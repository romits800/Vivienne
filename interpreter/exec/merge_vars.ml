open Eval
open Pc_type
open Source
   
module LoopVarMap = Map.Make(struct
                   type t = string
                   let compare = compare
                 end)


let get_policy_loopvar = function
  | LocalVar (x,is_low,mo) -> is_low
  | GlobalVar (x,is_low,mo) -> is_low
  | StoreVar (sv, ty, sz, is_low, mo) -> is_low
    
(* Merge new variables *)
let  merge_vars (lv: loopvar_t list) : loopvar_t list =
  let rec merge_vars_i (lv: loopvar_t list)
            (mp: loopvar_t LoopVarMap.t) : loopvar_t list =
    match lv with
    | (LocalVar (x,is_low,mo) as lvh) :: lvs ->
       let str = "Local" ^ string_of_int (Int32.to_int x.it) in 
       (try
          let is_low_old = get_policy_loopvar (LoopVarMap.find str mp) in
          if (is_low_old = is_low) then
              merge_vars_i lvs mp
          else (
              let mp' = LoopVarMap.add str (LocalVar (x,false,mo)) mp in
              merge_vars_i lvs mp'
          )
        with Not_found ->
          let mp' = LoopVarMap.add str lvh mp in
          merge_vars_i lvs mp'
       )
    | (GlobalVar (x,is_low,mo) as lvh) :: lvs ->
       let str = "Global" ^ string_of_int (Int32.to_int x.it) in
       (try
          let is_low_old = LoopVarMap.find str mp |> get_policy_loopvar in
          if (is_low_old = is_low) then 
              merge_vars_i lvs  mp
          else (
              let mp' = LoopVarMap.add str (GlobalVar (x,false,mo)) mp in
              merge_vars_i lvs  mp'
          )
        with Not_found ->
          let mp' = LoopVarMap.add str lvh mp in
          merge_vars_i lvs mp'
       )

    (* merge store only when they happen in consecutive loops - 
       otherwise the local/global variables take care of it
       take care of it *)
    | (StoreVar (sv, ty, sz, is_low, mo) as lvh) :: lvs ->
       if (!Flags.debug) then
           print_loopvar lvh;
       let str = "Store" ^ svalue_to_string sv in
       (try
          let is_low_old = LoopVarMap.find str mp |> get_policy_loopvar in
          if (is_low_old = is_low) then
              merge_vars_i lvs mp
          else (
              let mp' = LoopVarMap.add str (StoreVar (sv, ty, sz, false, mo)) mp in
              merge_vars_i lvs mp'
          )
       with Not_found ->
         let mp' = LoopVarMap.add str lvh mp in
         (* merge_vars_i lvs (lvh::acc) mp' *)
         merge_vars_i lvs mp'
       )
    | [] -> LoopVarMap.bindings mp |> List.map (fun (k,v) -> v) 
         
  in
  if (!Flags.debug) then 
      print_endline "Merging variables";
  let mp = LoopVarMap.empty in
  merge_vars_i lv mp
