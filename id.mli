
type t

val compare : t -> t -> int
val print : t -> string

(* Constructor *)
val create : unit -> t
val from_string : string -> t
val from_int : int -> t

(* Destructor *)
val string_of : t -> string
val int_of : t -> int

val const : t

(* Serializer *)
val serialize : t -> string
val deserialize : string -> t
