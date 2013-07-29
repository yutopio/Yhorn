open Types

type 'a t = 'a formula

let rec flatten =
  function
  | Expr (Expr x) -> Expr x
  | Expr (And x) -> And x
  | Expr (Or x) -> Or x
  | And x -> And (List.map flatten x)
  | Or x -> Or (List.map flatten x)
