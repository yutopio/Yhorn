open Types

exception Satisfiable of (Id.t * int) list

type space (* = pexpr nf * Constr.constrSet *)

val interpolate : expr formula * expr formula -> space
val getInterpolant : space -> expr formula
val verifyInterpolant : expr formula * expr formula -> expr formula -> unit
