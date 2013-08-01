open MTypes
open Types

exception Unsatisfiable of string list

val solve : (string * Expr.t Formula.t) list -> int M.t
val check_interpolant :
  Expr.t Formula.t * Expr.t Formula.t -> Expr.t Formula.t -> bool
val check_clause : hornSol -> horn -> bool
