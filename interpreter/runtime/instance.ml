open Types


type length = int
            
type module_inst =
{
  types : func_type list;
  funcs : func_inst list;
  tables : table_inst list;
  memories : memory_inst list;
  (* TODO(Romy): for now support one memory - the rest are instances. *)
  smemories : smemory_inst list;
  smemlen : length;
  globals : global_inst list;
  exports : export_inst list;
  secrets : security_inst list;
  public  : security_inst list;
}

and func_inst = module_inst ref Func.t
and table_inst = Table.t
and memory_inst = Memory.t
and smemory_inst = Smemory.t
and global_inst = Global.t
and export_inst = Ast.name * extern
and security_inst = int * int

and extern =
  | ExternFunc of func_inst
  | ExternTable of table_inst
  | ExternMemory of memory_inst
  | ExternSmemory of smemory_inst
  | ExternGlobal of global_inst

type Table.elem += FuncElem of func_inst


(* Auxiliary functions *)

let empty_module_inst =
  { types = []; funcs = []; tables = []; memories = []; smemories = []; smemlen = 0;
    globals = []; exports = []; secrets = []; public = []}

let extern_type_of = function
  | ExternFunc func -> ExternFuncType (Func.type_of func)
  | ExternTable tab -> ExternTableType (Table.type_of tab)
  | ExternMemory mem -> ExternMemoryType (Memory.type_of mem)
  | ExternSmemory mem -> ExternSmemoryType (Smemory.type_of mem)
  | ExternGlobal glob -> ExternGlobalType (Global.type_of glob)

let export inst name =
  try Some (List.assoc name inst.exports) with Not_found -> None
