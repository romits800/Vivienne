open Eval
open Svalues
open Types
open Source
open Pc_type

let rec havoc_vars (lv: loopvar_t list) (c : config) : config =
  if !Flags.debug then (
    print_endline "Havocing Variables..";
  );
  match lv with
  | LocalVar (x, is_low, mo) :: lvs ->
     let v = local c.frame x in
     (* let mem = (c.frame.inst.smemories, smemlen c.frame.inst) in *)
     (* let is_low = Z3_solver.is_v_ct_unsat c.pc v mem in *)
     let newv =
       (match v with
        | SI32 _ -> SI32 (if is_low then Si32.of_low() else Si32.of_high())
        | SI64 _ -> SI64 (if is_low then Si64.of_low() else Si64.of_high())
        | _ -> failwith "not implemented floated numbers"
       )
     in
     if !Flags.debug then (
        print_endline "New val";
        print_endline (svalue_to_string newv);
     );
 
     let c' = { c with frame = update_local c.frame x newv } in
     (* let c'' =
      *   match newv, mo with
      *   | SI32 nv, Increase (SI32 v) ->
      *      { c' with pc = (fst c'.pc, PCAnd(SI32 (Si32.ge_u nv v), snd c'.pc)) }
      *   | SI32 nv, Decrease (SI32 v) ->
      *      { c' with pc = (fst c'.pc, PCAnd(SI32 (Si32.le_u nv v), snd c'.pc)) }
      *   | SI64 nv, Increase (SI64 v) ->
      *      { c' with pc = (fst c'.pc, PCAnd(SI64 (Si64.ge_u nv v), snd c'.pc)) }
      *   | SI64 nv, Decrease (SI64 v) ->
      *      { c' with pc = (fst c'.pc, PCAnd(SI64 (Si64.le_u nv v), snd c'.pc)) }
      *   (\* | _, Nothing -> c' *\)
      *   | _ -> c'
      * in *)
     havoc_vars lvs c'
  | GlobalVar (x, is_low, mo) :: lvs ->
     let v = Sglobal.load (sglobal c.frame.inst x) in
     (* let mem = (c..inst.smemories, smemlen c.frame.inst) in *)
     (* let is_low = Z3_solver.is_v_ct_unsat c.pc v mem in *)
     let newv =
       (match v with
        | SI32 _ -> SI32 (if is_low then Si32.of_low() else Si32.of_high())
        | SI64 _ -> SI64 (if is_low then Si64.of_low() else Si64.of_high())
        | _ -> failwith "not implemented floated numbers"
       )
     in
     let newg = 
       (try Sglobal.store (sglobal c.frame.inst x) newv
        with Sglobal.NotMutable -> Crash.error x.at "write to immutable global"
           | Sglobal.Type -> Crash.error x.at "type mismatch at global write")
     in
     
     let c' = { c with frame = {c.frame with inst = update_sglobal c.frame.inst newg x } } in
     (* let c'' =
      *   match newv, mo with
      *   | SI32 nv, Increase (SI32 v) ->
      *      { c' with pc = (fst c'.pc, PCAnd(SI32 (Si32.ge_u nv v), snd c'.pc)) }
      *   | SI32 nv, Decrease (SI32 v) ->
      *      { c' with pc = (fst c'.pc, PCAnd(SI32 (Si32.le_u nv v), snd c'.pc)) }
      *   | SI64 nv, Increase (SI64 v) ->
      *      { c' with pc = (fst c'.pc, PCAnd(SI64 (Si64.ge_u nv v), snd c'.pc)) }
      *   | SI64 nv, Decrease (SI64 v) ->
      *      { c' with pc = (fst c'.pc, PCAnd(SI64 (Si64.le_u nv v), snd c'.pc)) }
      *   (\* | _, Nothing -> c' *\)
      *   | _ -> c'
      * in *)

     havoc_vars lvs c'
  | StoreVar (SI32 addr' as addr, ty, sz, is_low, mo) :: lvs when Si32.is_int addr' ->

     let sv =
       (match ty with
        |Types.I32Type ->
          SI32 (if is_low then Si32.of_low() else Si32.of_high())
        |Types.I64Type ->
          SI64 (if is_low then Si64.of_low() else Si64.of_high())
        | _ -> failwith "not implemented float types"
       )
     in          
     if !Flags.debug then (
        print_endline "New val store:";
        print_loopvar (StoreVar (addr, ty, sz, is_low, mo));
        print_endline (svalue_to_string sv);
     );
     let num = Instance.next_num() in
     let nv =
       (match sz with
        | None ->
           Eval_symbolic.eval_store ty addr sv
             (smemlen c.frame.inst) num (Types.size ty)
        | Some (sz) ->
           assert (packed_size sz <= Types.size ty);
           let n = packed_size sz in
           Eval_symbolic.eval_store ty addr sv
             (smemlen c.frame.inst) num n 
       )
     in
     let mem = smemory c.frame.inst (0l @@ Source.no_region) in
     let mem' = Smemory.store_sind_value num mem nv in

           (*let mem = (havc.frame.inst.smemories, smemlen havc.frame.inst) in*)

     let nframe  = {c.frame with inst = insert_smemory c.frame.inst num mem'} in

     let c' = { c with frame = nframe} in

(*     let c'' =
       match nv, mo with
       | SI32 nv, Increase (SI32 v) ->
          { c' with pc = (fst c'.pc, PCAnd(SI32 (Si32.ge_u nv v), snd c'.pc)) }
       | SI32 nv, Decrease (SI32 v) ->
          { c' with pc = (fst c'.pc, PCAnd(SI32 (Si32.le_u nv v), snd c'.pc)) }
       | SI64 nv, Increase (SI64 v) ->
          { c' with pc = (fst c'.pc, PCAnd(SI64 (Si64.ge_u nv v), snd c'.pc)) }
       | SI64 nv, Decrease (SI64 v) ->
          { c' with pc = (fst c'.pc, PCAnd(SI64 (Si64.le_u nv v), snd c'.pc)) }
       (* | _, Nothing -> c' *)
       | _ -> c'
     in
*)
     havoc_vars lvs c'
  | StoreVar _ :: lvs -> havoc_vars lvs c
  | [] -> c
                
