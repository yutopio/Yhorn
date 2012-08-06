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

type coefMap = Dictionary<string, float>

type formula2 =
    | One of bool * coefMap
    | Many of formula2 list

type nf = (bool * coefMap) list list
