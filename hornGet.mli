open Types

val assignParameters: int M.t -> pexpr -> expr
val getSolution : (Id.t * Id.t) list -> hornSolSpace -> hornSol
