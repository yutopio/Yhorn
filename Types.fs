module Types

open System
open System.Collections.Generic
open Error

type term = float * string
type expr = int * term list * term list
type formula =
    | Expr of expr
    | And of formula list
    | Or of formula list

type coef = Dictionary<string, float>
type expr2 = bool * coef
type formula2 =
    | One of expr2
    | Many of formula2 list
type nf = expr2 list list
