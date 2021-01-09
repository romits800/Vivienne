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
    | (LocalVar (x,_,mo) as lvh) :: lvs ->
       let str = "Local" ^ string_of_int (Int32.to_int x.it) in
       (try
          let _ = LoopVarMap.find str mp in
          merge_vars_i lvs acc mp
        with Not_found ->
          let mp' = LoopVarMap.add str true mp in
          merge_vars_i lvs (lvh::acc) mp'
            
       )
    | (GlobalVar (x,_,mo) as lvh) :: lvs ->
       let str = "Global" ^ string_of_int (Int32.to_int x.it) in
       (try
          let _ = LoopVarMap.find str mp in
          merge_vars_i lvs acc mp
        with Not_found ->
          let mp' = LoopVarMap.add str true mp in
          merge_vars_i lvs (lvh::acc) mp'
       )

    | (StoreVar (sv, ty, sz, is_low, mo) as lvh) :: lvs ->
       let str = "Store" ^ svalue_to_string sv in
       (try
          let _ = LoopVarMap.find str mp in
          merge_vars_i lvs acc mp
       with Not_found ->
         let mp' = LoopVarMap.add str true mp in
         merge_vars_i lvs (lvh::acc) mp'
            
       )
    | [] -> acc
         
  in
  let mp = LoopVarMap.empty in
  merge_vars_i lv [] mp
