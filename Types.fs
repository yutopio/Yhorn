module Types

open System
open System.Collections.Generic
open Error

type term = float * string option
type expr = int * term list * term list
type clauses =
    | Expr of expr
    | And of expr * expr
    | Or of expr * expr
