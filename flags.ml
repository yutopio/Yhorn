
(* Z3 query timeout specified in milliseconds. *)
let z3_timeout = ref 5000

(******************************************************************************)
(*** Debug flags **************************************************************)
(******************************************************************************)

(* Enable gv to show intermediate graph representations. *)
let enable_gv = ref false

(* Rename all variables in input. Convenient to debug intermediate Horn clause
   solving problems appearing in verification process since they may contain
   unparsable predicate names in their raw input. *)
let rename_input = ref false

(* If true, print Z3 AST query before it is checked. *)
let print_z3_ast = ref false

(* If true, show detail on every query on integer programming. *)
let debug_z3_ip = ref false

(* If true, integer programming is performed for constraint solving. Otherwise
   performed on real space. *)
let integer_programming = ref true
