open Types

val assignParameters: int M.t -> pexpr -> expr
val solve : horn list -> (Id.t * Id.t) list -> hornSol
