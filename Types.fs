module Types

open System
open System.Collections.Generic
open Error

type operator =
    | EQ
    | NEQ
    | LT
    | LTE
    | GT
    | GTE

type term = int * string
type expr = operator * term list * term list
type formula =
    | Expr of expr
    | And of formula list
    | Or of formula list

type coef = Dictionary<string, int>
type expr2 = operator * coef
type formula2 =
    | One of expr2
    | Many of formula2 list
type nf = expr2 list list
