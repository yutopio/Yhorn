module Main

open System
open System.Collections.Generic
open System.Linq
open Parser
open Types

// This procedure sums up all terms according to the variable and move to the
// left-side of the expression. It also flips "<" and "<=" operators to ">" and
// ">=". Returns the operator number (2 >, 3 <>, 4 =, 6 >=) and the mapping from
// a variable to its coefficient. The constant has empty string as a key.
let normalizeExpr (op, t1, t2) =
    let coefs = new Dictionary<string, float>() in
    let addCoef sign (coef, var) =
        let key = match var with Some x -> x | None -> "" in
        coefs.[key] <-
            if coefs.ContainsKey(key) then
                coefs.[key] + sign * coef
            else sign * coef
    List.iter (addCoef (if op % 2 = 0 then 1. else -1.)) t1;
    List.iter (addCoef (if op % 2 = 0 then -1. else 1.)) t2;
    (if op = 1 || op = 5 then op + 1 else op), coefs

// Copies the given mapping with sign of every coefficient reversed.
let invert (coefs:Dictionary<string, float>) =
    let r = new Dictionary<string, float>(coefs) in
    Array.iter (fun k -> r.[k] <- -r.[k]) (coefs.Keys.ToArray()); r

// This procedure normalizes all formulae by sorting out its coefficients, and
// reduces the kinds of operators into only >= and >. It returns the tree
// data structure formed by formula2. The equality is stored as the first value
// of One construct, which appears as the leaf of the tree.
let rec normalizeGroupInternal opAnd formulae ret =
    match formulae with
    | [] -> ret
    | x :: l ->
        let elem = match x with
            | Expr x ->
                let (op, coefs) = normalizeExpr x in
                let pair eq = [One (eq, coefs); One (eq, invert coefs)] in
                match op with
                | 2 -> [One (false, coefs)]
                | 3 -> let l = pair false in if opAnd then [Many l] else l
                | 4 -> let l = pair true in if opAnd then l else [Many l]
                | 6 -> [One (true, coefs)]
            | And x -> [Many (normalizeGroupInternal true x [])]
            | Or x -> [Many (normalizeGroupInternal false x [])] in
        normalizeGroupInternal opAnd l (elem @ ret)
let normalizeOperator formulae =
    match formulae with
    | Expr _ -> normalizeGroupInternal false [ formulae ] []
    | And x -> [ Many (normalizeGroupInternal true x []) ]
    | Or x -> normalizeGroupInternal false x []

let test = "x + y > 2 & y - 2z < 0 & 3x - z >= 5 ; 2x - y + 3z <= 0"
let (g1, g2) = inputUnit Lexer.token (Lexing.LexBuffer<char>.FromString(test))
let norm = List.map normalizeOperator [g1 ; g2]
