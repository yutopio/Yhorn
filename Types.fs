module Types

open System
open System.Collections.Generic
open Error

type term = float * string option
type expr = int * term list * term list
type formula =
    | Expr of expr
    | And of formula list
    | Or of formula list
