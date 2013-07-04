
type t =
  | NumId of int
  | StrId of string
  | Special

let id = ref 0

let compare = compare

let print = function
  | NumId x -> "$" ^ string_of_int x
  | StrId x -> x
  | Special -> "~"

let create () = incr id; NumId !id

let from_string x = StrId x

let from_int x = NumId x

let string_of = function
  | StrId x -> x
  | _ -> assert false

let int_of = function
  | NumId x -> x
  | _ -> assert false

let const = Special

let serialize = function
  | NumId x -> "N" ^ string_of_int x
  | StrId x -> "S" ^ x
  | Special -> "C"

let deserialize x =
  match x.[0] with
  | 'N' -> NumId (int_of_string (String.sub x 1 (String.length x - 1)))
  | 'S' -> StrId (String.sub x 1 (String.length x - 1))
  | 'C' -> Special
