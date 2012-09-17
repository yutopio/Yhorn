
open Map

module String = struct
  type t = string
  let compare = compare
end
type operator =
    | EQ
    | NEQ
    | LT
    | LTE
    | GT
    | GTE

module M = Map.Make(String)

type term = int * string
type expr = operator * term list * term list
type formula =
    | Expr of expr
    | And of formula list
    | Or of formula list

type coef = int M.t
type expr2 = operator * coef
type formula2 =
    | One of expr2
    | Many of formula2 list
type nf = expr2 list list
