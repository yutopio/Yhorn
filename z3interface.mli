open Types

val check_formula : expr formula -> bool option
val integer_programming : expr formula -> int M.t option
val check_interpolant : expr formula * expr formula -> expr formula -> bool
val check_clause : hornSol -> horn -> bool
