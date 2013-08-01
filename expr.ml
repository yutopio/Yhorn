open MTypes
open Util

type operator =
| EQ
| NEQ
| LT
| LTE
| GT
| GTE

let negateOp =
  function
  | EQ -> NEQ
  | NEQ -> EQ
  | LT -> GTE
  | LTE -> GT
  | GT -> LTE
  | GTE -> LT

let operator_of_string =
  function
  | "=" -> EQ
  | "<>" -> NEQ
  | "<" -> LT
  | "<=" -> LTE
  | ">" -> GT
  | ">=" -> GTE

let string_of_operator =
  function
  | EQ -> "="
  | NEQ -> "<>"
  | LT -> "<"
  | LTE -> "<="
  | GT -> ">"
  | GTE -> ">="

type coef = int M.t

let coefOp op d = M.fold (M.addDefault d op)
let (++) = coefOp (+) 0
let (--) x y = coefOp (-) 0 y x (* Note that the operands need to be reversed. *)
let (~--) = M.map (~-)

type t = operator * coef

let comp (o1, c1) (o2, c2) =
  match compare o1 o2 with
  | 0 -> M.compare compare c1 c2
  | x -> x
