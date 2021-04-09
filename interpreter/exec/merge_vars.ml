open Eval
open Pc_type
open Source
   
module LoopVarMap = Map.Make(struct
                   type t = string
                   let compare = compare
                 end)

(* Merge new variables *)
let  merge_vars (lv: loopvar_t list) : loopvar_t list =
  let rec merge_vars_i (lv: loopvar_t list) (acc: loopvar_t list) mp : loopvar_t list =
    match lv with
    | (LocalVar (x,is_low,mo) as lvh) :: lvs ->
       let str = "Local" ^ string_of_int (Int32.to_int x.it) in (* ^ string_of_bool is_low in*)
       (try
          let is_low_old = LoopVarMap.find str mp in
          if (is_low_old = is_low) then
              merge_vars_i lvs (lvh::acc) mp
          else (
              let mp' = LoopVarMap.add str false mp in
              merge_vars_i lvs (LocalVar (x,false,mo)::acc) mp'
          )
        with Not_found ->
          let mp' = LoopVarMap.add str is_low mp in
          merge_vars_i lvs acc mp'
       )
    | (GlobalVar (x,is_low,mo) as lvh) :: lvs ->
       let str = "Global" ^ string_of_int (Int32.to_int x.it) in
       (try
          let is_low_old = LoopVarMap.find str mp in
          if (is_low_old = is_low) then 
              merge_vars_i lvs (lvh::acc) mp
          else (
              let mp' = LoopVarMap.add str false mp in
              merge_vars_i lvs (GlobalVar(x,false,mo)::acc) mp'
          )
        with Not_found ->
          let mp' = LoopVarMap.add str is_low mp in
          merge_vars_i lvs acc mp'
       )

    (* merge store only when they happen in consecutive loops - 
       otherwise the local/global variables take care of it
       take care of it *)
    | (StoreVar (sv, ty, sz, is_low, mo) as lvh) :: lvs ->
       if (!Flags.debug) then
           print_loopvar lvh;
       let str = "Store" ^ svalue_to_string sv in
       (try
          let is_low_old = LoopVarMap.find str mp in
          if (is_low_old = is_low) then
              merge_vars_i lvs (lvh::acc) mp
          else (
              let mp' = LoopVarMap.add str false mp in
              merge_vars_i lvs (StoreVar (sv, ty, sz, false, mo)::acc) mp'
          )
       with Not_found ->
         let mp' = LoopVarMap.add str is_low mp in
         (* merge_vars_i lvs (lvh::acc) mp' *)
         merge_vars_i lvs acc mp'
       )
    | [] -> acc
         
  in
  if (!Flags.debug) then 
      print_endline "Merge vars";
  let mp = LoopVarMap.empty in
  merge_vars_i lv [] mp
