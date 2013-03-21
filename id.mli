
type t

val print : t -> string
val compare : t -> t -> int

(* Constructor *)
val create : unit -> t
val from_string : string -> t
val from_int : int -> t

(* Destructor *)
val string_of : t -> string
val int_of : t -> int

val const : t
