
type t =
  | NumId of int
  | StrId of string
  | Special

let id = ref 0

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
