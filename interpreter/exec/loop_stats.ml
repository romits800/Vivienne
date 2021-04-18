open Ast
open Source
open Config
   
type stats_t = {
    number_modified: int;
    possible_loop_iterations: int;
    number_instructions: int;
    number_calls: int;
    number_ifs: int;
    number_mem_ops: int;
  }

let init_stats () =
  { number_modified = 0;
    possible_loop_iterations = 0;
    number_instructions = 0;
    number_calls = 0;
    number_ifs = 0;
    number_mem_ops = 0 }
  
let increase_instr stats =
  {stats with number_instructions = stats.number_instructions + 1} 

let increase_mv stats =
  {stats with number_modified = stats.number_modified + 1} 

let increase_calls stats =
  {stats with number_calls = stats.number_calls + 1} 

let increase_ifs stats =
  {stats with number_ifs = stats.number_ifs + 1} 

let increase_mem stats =
  {stats with number_mem_ops = stats.number_mem_ops + 1} 


let increase_loop_iter x stats =
  let new_const = 
    match x with
    | Values.I32 i -> Int32.to_int i
    | Values.I64 i -> Int64.to_int i
    | _ -> failwith "Not supporting floats"
  in
  if stats.possible_loop_iterations < new_const && new_const < magic_number_max_loop then
    {stats with possible_loop_iterations = new_const}
  else stats

module StatsMap = Map.Make(struct
                      type t = int
                      let compare = (-)
                    end)

let statsmap = ref StatsMap.empty  

let init_statsmap () =
  statsmap := StatsMap.empty


let loop_stats (es : Ast.instr list ) (reg: Source.region) : stats_t option =
  let rec loop_stats_i (es : Ast.instr list ) (stats : stats_t) : stats_t =
    (match es with
     | e'::est ->
        (match e'.it with
         | Unreachable ->
            loop_stats_i est (increase_instr stats) 
         | Nop ->
            loop_stats_i est (increase_instr stats) 
         | Block (bt, es') ->
            loop_stats_i (es' @ est) (increase_instr stats) 
         | Loop (bt, es') ->
            loop_stats_i (es' @ est) (increase_instr stats) 
         | If (bt, es1, es2) ->
            loop_stats_i est (stats |> increase_instr |> increase_ifs)
         | Br x ->
            loop_stats_i est (increase_instr stats) 
         | BrIf x->
            loop_stats_i est (stats |> increase_instr |> increase_ifs)
         | Return ->
            loop_stats_i est (increase_instr stats) 
         | Call x ->
            (*TODO(Romy): not taken into consideration*)
            loop_stats_i est (stats |> increase_instr |> increase_calls)
         | Drop->
            loop_stats_i est (increase_instr stats) 
         | Select->
            loop_stats_i est (increase_instr stats) 
         | LocalGet x ->
            loop_stats_i est (increase_instr stats) 
         | LocalSet x->
            loop_stats_i est (stats |> increase_instr |> increase_mv)
         | LocalTee x->
            loop_stats_i est (stats |> increase_instr |> increase_mv)
         | GlobalGet x ->
            loop_stats_i est (increase_instr stats) 
         | GlobalSet x->
            loop_stats_i est (stats |> increase_instr |> increase_mv)
         | Load {offset; ty; sz; _}->
            loop_stats_i est (increase_instr stats |> increase_mem) 
         | Store {offset; ty; sz; _}->
            loop_stats_i est (stats |> increase_instr |> increase_mv |> increase_mem)
         | Const v ->
            loop_stats_i est (stats |> increase_instr |> increase_loop_iter v.it)
         | Test testop->
            loop_stats_i est (increase_instr stats) 
         | Compare relop->
            loop_stats_i est (increase_instr stats) 
         | Unary unop->
            loop_stats_i est (increase_instr stats) 
         | Binary binop->
            loop_stats_i est (increase_instr stats) 
         | Convert cvtop->
            loop_stats_i est (increase_instr stats) 
         | _ ->
            loop_stats_i est (increase_instr stats) 
        )
     | [] -> stats
    )
  in
  let line = reg.left.line in
  try
    let _ = StatsMap.find line !statsmap in
    None
  with Not_found->
    let stats = loop_stats_i es (init_stats()) in
    statsmap := StatsMap.add line stats !statsmap;
    Some stats

let select_invar stats =
  true
  (*let open Config in
  if stats.possible_loop_iterations > magic_number_si_loop_iter &&
       stats.number_modified < magic_number_si_mod_vars &&
         stats.number_instructions > magic_number_si_instr then
    true
  else false *)
