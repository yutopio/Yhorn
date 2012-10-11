open Types

val fabs : float -> float
val tryPick : ('a -> 'b option) -> 'a list -> 'b option
val addDefault : M.key -> 'a -> 'b -> ('b -> 'a -> 'b) -> 'b M.t -> 'b M.t
val printExpr2 : string -> expr2 -> unit
val printMatrix : string -> int array array -> unit
val printVector : string -> int array -> unit
val directProduct : 'a list list -> 'a list list
val normalizeExpr : operator * (int * string) list * (int * string) list -> expr2
val convertToDNF : formula -> expr2 nf
val coefOp : (int -> 'a -> int) -> 'a M.t -> int M.t -> int M.t
val invert : coef -> coef
val getSpace : (bool * expr2) list -> space
val getInterpolant : space -> expr2 option
val solve : expr2 list -> expr2 list -> space option