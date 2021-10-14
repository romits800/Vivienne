let interactive = ref false
let trace = ref false
let unchecked = ref false
let print_sig = ref false
let dry = ref false
let width = ref 80
let harness = ref true
let bfs = ref false
let pfs = ref false
let loop_invar = ref false
let simplify = ref false
let select_unsafe = ref false
let elim_induction_variables = ref false
let stats = ref false
let unroll_one = ref false
let no_clean = ref false
let explicit_leaks = ref false
let debug = ref false
let estimate_loop_size = ref false
let replace_expressions = ref (-1)
let merge_states = ref 4
let exclude_zero_address = ref false
let end_of_ro_data = ref (-1)
let generate_model = ref false
let magic_number_2 = ref 1000
let magic_number_1 = ref 1000
let very_small_num_expr = ref 100


type solver_id_t = MIXED | PORTFOLIO | Z3_BINDINGS | Z3 | CVC4 | BITWUZLA | BOOLECTOR | YICES2 

let solver = ref MIXED

let set_solver = function
  | "portfolio"   -> solver := PORTFOLIO
  | "z3_bindings" -> solver := Z3_BINDINGS
  | "z3"          -> solver := Z3
  | "cvc4"        -> solver := CVC4
  | "boolector"   -> solver := BOOLECTOR
  | "bitwuzla"    -> solver := BITWUZLA
  | "yices2"      -> solver := YICES2                 
  | _             -> solver := MIXED
