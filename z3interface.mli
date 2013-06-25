open Types

exception Unsatisfiable of string list

val solve : (string * expr formula) list -> int M.t
val check_interpolant : expr formula * expr formula -> expr formula -> bool
val check_clause : hornSol -> horn -> bool
