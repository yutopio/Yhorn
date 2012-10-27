
open Buffer
open Map
open Util

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

let printExpr ?(vars = None) (op, coef) =
    let z3, vars = match vars with
        | Some vars -> true, vars
        | None -> false, ref [] in

    let buf = create 1 in
    let first = ref true in
    M.iter (fun v c ->
        if (not z3 & v = "") || c = 0 then () else (
        if not (List.mem v !vars) then vars := v :: !vars;
        if c > 0 && not !first then add_char buf '+' else if c = -1 then add_char buf '-';
        first := false;
        if (abs c) <> 1 then add_string buf (let c = string_of_int c in if z3 then c ^ "*" else c);
        add_string buf v)) coef;
    if !first then add_string buf "0";
    add_string buf (string_of_operator op);
    add_string buf (if z3 then "0" else string_of_int (-(M.find "" coef)));
    contents buf
    
type 'a formula =
    | Expr of 'a
    | And of 'a formula list
    | Or of 'a formula list

let rec printFormula elementPrinter x =
    match x with
    | Expr x -> elementPrinter x
    | And x -> join " & " (List.map (fun x -> "(" ^ (printFormula elementPrinter x) ^ ")") x)
    | Or x -> join " | " (List.map (fun x -> "(" ^ (printFormula elementPrinter x) ^ ")") x)

type 'a nf = 'a list list
type space = (operator M.t * coef M.t) * expr formula
