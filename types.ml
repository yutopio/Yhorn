
open Map

module String = struct
  type t = string
  let compare = compare
end

module M = Map.Make(String)

module Integer = struct
  type t = int
  let compare = compare
end

module MI = Map.Make(Integer)

type term = float * string
type expr = int * term list * term list
type formula =
    | Expr of expr
    | And of formula list
    | Or of formula list

type coef = float M.t
type expr2 = bool * coef
type formula2 =
    | One of expr2
    | Many of formula2 list
type nf = expr2 list list
