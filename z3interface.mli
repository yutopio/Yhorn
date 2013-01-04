open Types

val integer_programming : expr formula -> int M.t option
val check_clause : hornSol -> horn -> bool
