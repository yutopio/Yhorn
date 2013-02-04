open Types

exception Satisfiable of (Id.t * int) list

type space

val interpolate : expr formula * expr formula -> space
val intersect : space list -> space
val getInterpolant : space -> expr formula
val verifyInterpolant : expr formula * expr formula -> expr formula -> unit
