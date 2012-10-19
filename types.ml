
open Map

module String = struct
  type t = string
  let compare = compare
end

module M = Map.Make(String)

type operator =
    | EQ
    | NEQ
    | LT
    | LTE
    | GT
    | GTE

let string_of_operator = function
    | EQ -> "=="
    | NEQ -> "!="
    | LT -> "<"
    | LTE -> "<="
    | GT -> ">"
    | GTE -> ">="

type coef = int M.t
type expr = operator * coef
type 'a formula =
    | Expr of 'a
    | And of 'a formula list
    | Or of 'a formula list

type 'a nf = 'a list list

type space = (operator * coef M.t) * expr formula
