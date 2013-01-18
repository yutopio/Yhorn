open Types

val getSpace : (bool * expr) list -> space
val getInterpolant : space formula -> expr formula option
val mergeSpace : bool -> space formula -> space formula -> space formula
val interpolate : expr formula list -> space formula option
val verifyInterpolant : expr formula * expr formula -> expr formula -> unit
