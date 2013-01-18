open Types

val integer_programming : expr formula -> int M.t option
val check_interpolant : expr formula * expr formula -> expr formula -> bool
val check_clause : hornSol -> horn -> bool
