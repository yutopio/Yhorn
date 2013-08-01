open Expr
open MTypes
open Types

val assignParameters: int M.t -> pcoef -> coef
val solve : horn list -> hornSol
