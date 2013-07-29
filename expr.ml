open Types

type t = expr

let compare (o1, c1) (o2, c2) =
  match compare o1 o2 with
  | 0 -> M.compare compare c1 c2
  | x -> x
