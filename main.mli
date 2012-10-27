open Types

val addDefault : M.key -> 'a -> 'b -> ('b -> 'a -> 'b) -> 'b M.t -> 'b M.t
val convertToDNF : expr formula -> expr nf
val coefOp : (int -> 'a -> int) -> 'a M.t -> int M.t -> int M.t
val invert : coef -> coef
val getSpace : (bool * expr) list -> space
val getInterpolant : space formula -> expr formula option
val solve : expr list -> expr list -> space formula option
val intersectSpace : space formula -> space formula -> space formula
