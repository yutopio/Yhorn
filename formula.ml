open Types

type 'a t = 'a formula

let rec flatten =
  function
  | Term (Term x) -> Term x
  | Term (And x) -> And x
  | Term (Or x) -> Or x
  | And x -> And (List.map flatten x)
  | Or x -> Or (List.map flatten x)
