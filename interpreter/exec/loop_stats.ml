open Ast
open Source
open Config
open Eval
   
type stats_t = {
    number_modified: int;
    possible_loop_iterations: int;
    number_instructions: int;
    number_calls: int;
    number_ifs: int;
    number_mem_ops: int;
    stack_instructions: Ast.instr list;
    possible_store_indexes: (Ast.instr * Ast.instr * Svalues.svalue option) list;
    modified_variables: loopvar_t list;
  }

let init_stats () =
  { number_modified = 0;
    possible_loop_iterations = 0;
    number_instructions = 0;
    number_calls = 0;
    number_ifs = 0;
    number_mem_ops = 0;
    stack_instructions = [];
    possible_store_indexes = [];
    modified_variables = []}
  
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

let add_instruction v stats =
  {stats with stack_instructions = v::stats.stack_instructions}

let remove_instruction stats =
  match stats.stack_instructions with
  | s::ss -> {stats with stack_instructions = ss}
  | [] -> stats

let remove_two_instructions stats =
  match stats.stack_instructions with
  | s1::s2::ss -> {stats with stack_instructions = ss}
  | _ -> stats

let remove_three_instructions stats =
  match stats.stack_instructions with
  | s1::s2::s3::ss -> {stats with stack_instructions = ss}
  | _ -> stats

let add_store_index st stats =
  match stats.stack_instructions with
  | v1::v2::vs -> {stats with possible_store_indexes = (v2,st,None)::stats.possible_store_indexes}
  | _ -> stats

let get_store_index stats =
  match stats.stack_instructions with
  | v1::v2::vs -> Some v2
  | _ -> None

       
       

let add_mod_var var stats =
  {stats with modified_variables = var::stats.modified_variables}
       
let get_store_indexes stats =
  stats.possible_store_indexes

let set_store_indexes stats indexes =
  {stats with possible_store_indexes = indexes }

let ast_instr_to_string = function
  | Unreachable         -> "Unreachable"
  | Nop                 -> "Nop"
  | Drop                -> "Drop"
  | Select              -> "Select"
  | Block _             -> "Block"
  | Loop _		-> "Loop"
  | If _		-> "If"
  | Br _		-> "Br"
  | BrIf _		-> "BrIf"
  | BrTable _		-> "BrTable"
  | Return              -> "Return"
  | Call _		-> "Call"
  | CallIndirect _	-> "CallIndirect"
  | LocalGet _		-> "LocalGet"
  | LocalSet _		-> "LocalSet"
  | LocalTee _		-> "LocalTee"
  | GlobalGet _		-> "GlobalGet"
  | GlobalSet _		-> "GlSet"
  | Load _		-> "Load"
  | Store _		-> "STore"
  | MemorySize          -> "MemorySize"
  | MemoryGrow          -> "MemoryGrow"
  | Const _		-> "Const"
  | Sconst _		-> "Sconst"
  | Test _		-> "Test"
  | Compare _		-> "Compare"
  | Unary _		-> "Unary"
  | Binary _		-> "Binary"
  | Convert _		-> "Convert"


let rec print_store_indexes indexes = 
    match indexes with
    ({it=LocalGet x;at},_) :: sts -> print_endline ("Local" ^ (string_of_int (I32.to_int_u x.it )));  print_store_indexes sts
    | ({it=LocalTee x;at},_) :: sts -> print_endline ("LocalTee" ^ (string_of_int (I32.to_int_u x.it )));  print_store_indexes sts
    | ({it=GlobalGet x;at},_) :: sts -> print_endline ("LocalTee" ^ (string_of_int (I32.to_int_u x.it )));  print_store_indexes sts
    | ({it= ins;at},_) :: sts -> print_endline (ast_instr_to_string ins); print_store_indexes sts
    | [] -> ()

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


let loop_stats (es : Ast.instr list ) (reg: Source.region) : stats_t = 
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
            loop_stats_i (es1 @ es2 @ est)
              (stats |> increase_instr |> increase_ifs |> remove_instruction)
         | Br x ->
            loop_stats_i est (increase_instr stats) 
         | BrIf x->
            loop_stats_i est (stats |> increase_instr |> increase_ifs |> remove_instruction)
         | Return ->
            loop_stats_i est (increase_instr stats) 
         | Call x ->
            (*TODO(Romy): not taken into consideration*)
            loop_stats_i est (stats |> increase_instr |> increase_calls)
         | Drop->
            loop_stats_i est (increase_instr stats |> remove_instruction) 
         | Select->
            loop_stats_i est (increase_instr stats |> remove_three_instructions)
         | LocalGet x ->
            loop_stats_i est (increase_instr stats |> add_instruction e') 
         | LocalSet x->
            loop_stats_i est (stats |> increase_instr |> increase_mv
                              |> add_mod_var (LocalVar(x,false,Nothing,None))
                              |> remove_instruction)
         | LocalTee x->
            loop_stats_i est (stats |> increase_instr |> increase_mv
                              |> add_mod_var (LocalVar(x,false,Nothing,None))
                              |> remove_instruction |> add_instruction e')
         | GlobalGet x ->
            loop_stats_i est (increase_instr stats |> add_instruction e') 
         | GlobalSet x->
            loop_stats_i est (stats |> increase_instr |> increase_mv
                              |> add_mod_var (GlobalVar(x,false,Nothing,None))
                              |> remove_instruction)
         | Load {offset; ty; sz; _}->
            loop_stats_i est (increase_instr stats |> increase_mem |> add_instruction e') 
         | Store {offset; ty; sz; _}->
            loop_stats_i est (stats |> increase_instr |> increase_mv |> increase_mem
                              |> add_mod_var (StoreVar(None,ty,sz,false,Nothing,e'.at))
                              |> add_store_index e' |> remove_two_instructions)
         | Const v ->
            loop_stats_i est (stats |> increase_instr |> increase_loop_iter v.it
                              |> add_instruction e')
         | Test testop->
            loop_stats_i est (increase_instr stats |> remove_instruction
                              |> add_instruction e') 
         | Compare relop->
            loop_stats_i est (increase_instr stats |> remove_two_instructions
                              |> add_instruction e') 
         | Unary unop->
            loop_stats_i est (increase_instr stats |> remove_instruction |> add_instruction e') 
         | Binary binop->
            loop_stats_i est (increase_instr stats |> remove_two_instructions
                              |> add_instruction e')
         | Convert cvtop->
            loop_stats_i est (increase_instr stats |> remove_instruction |> add_instruction e') 
         | CallIndirect x ->
            loop_stats_i est (increase_instr stats |> remove_instruction)
         (* | MemorySize ->
          *    loop_stats_i est (increase_instr stats |> remove_instruction)
          * | MemoryGrow ->
          *    loop_stats_i est (increase_instr stats |> remove_instruction)
          * | BrTable (xs,x) ->
          *   loop_stats_i est (increase_instr stats |> remove_instruction)
          * | Sconst x ->
          *   loop_stats_i est (increase_instr stats |> remove_instruction) *)
        | _ ->
            loop_stats_i est (increase_instr stats) 
        )
     | [] -> stats
    )
  in
  let line = reg.left.line in
  try
    let stats = StatsMap.find line !statsmap in
    stats
  with Not_found->
    let stats = loop_stats_i es (init_stats()) in
    statsmap := StatsMap.add line stats !statsmap;
    stats

let select_invar stats =
  let open Config in
  if stats.number_modified < magic_number_si_mod_vars (*&& *)
     (*(not !Flags.exclude_zero_address || stats.number_calls = 0)*)
  then
    true
  else false
