open Types

val assignParameters: int M.t -> pexpr -> expr
val solve : (Id.t * Id.t) list -> horn list -> hornSol
