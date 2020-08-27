(* open Values
 * open Instance *)

(* type symb = Integ of string | Bitmap of string | Real of string
 *
 * val init : string -> string -> symb *)
open Script
open Instance

val run : func_inst -> security' list -> string list

(* (\* type symbv
 *  * type expr = Symb of symbv
 *  *           (\\* Int *\\)
 *  *           | SClz of expr
 *  *           | SAdd of expr * expr
 *  *           | SSub of expr * expr
 *  *           | SMul of expr * expr
 *  *           | SDivS of expr * expr
 *  *           | SDivU of expr * expr
 *  *           | SRemS of expr * expr
 *  *           | SRemU of expr * expr
 *  *           | SAnd of expr * expr
 *  *           | SOr  of expr * expr
 *  *           | SXor of expr * expr
 *  *           | SShl of expr * expr
 *  *           | SShrS of expr * expr
 *  *           | SShrU of expr * expr
 *  *           | SRotl of expr * expr
 *  *           | SRotr of expr * expr
 *  *           (\\* Float only *\\)
 *  *           | SNeg of expr
 *  *           | SMin of expr * expr
 *  *           | SMax of expr * expr
 *  *           | SDiv of expr * expr
 *  *           | SCopySign of expr * expr
 *  *           (\\* Conditions *\\)
 *  *           | GeS of expr * expr
 *  *           | GeU of expr * expr
 *  *           | GtS of expr * expr
 *  *           | GtU of expr * expr
 *  *           | LeS of expr * expr
 *  *           | LeU of expr * expr
 *  *           | LtS of expr * expr
 *  *           | LtU of expr * expr
 *  *           | Eq of  expr * expr
 *  *           | Ne of  expr * expr
 *  *           (\\* Other *\\)
 *  *           | Ite of expr * expr * expr *\)
 *
 * type sstack
 * (\* Type of path condition*\)
 * type cond *)
