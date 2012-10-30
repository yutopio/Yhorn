open Types

val convertToDNF : expr formula -> expr nf
val coefOp : (int -> 'a -> int) -> 'a M.t -> int M.t -> int M.t
val invert : coef -> coef
val getSpace : (bool * expr) list -> space
val getInterpolant : space formula -> expr formula option
val mergeSpace : bool -> space formula -> space formula -> space formula
val solve : expr list -> expr list -> space formula option
val interpolate : expr formula list -> space formula option
val main: unit -> unit
