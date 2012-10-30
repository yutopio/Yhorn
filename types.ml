
open Buffer
open Map

module MyString = struct
  type t = string
  let compare = compare
end

module M = Map.Make(MyString)

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
        if v = "" || c = 0 then () else (
        if not (List.mem v !vars) then vars := v :: !vars;
        if c > 0 && not !first then add_char buf '+' else if c = -1 then add_char buf '-';
        first := false;
        if (abs c) <> 1 then add_string buf (let c = string_of_int c in if z3 then c ^ "*" else c);
        add_string buf v)) coef;
    if !first then add_string buf "0";
    add_string buf (string_of_operator op);
    add_string buf (if M.mem "" coef then string_of_int (-(M.find "" coef)) else "0");
    contents buf
    
type 'a formula =
    | Expr of 'a
    | And of 'a formula list
    | Or of 'a formula list

let rec printFormula elementPrinter x =
    match x with
    | Expr x -> elementPrinter x
    | And x -> String.concat " & " (List.map (fun x -> "(" ^ (printFormula elementPrinter x) ^ ")") x)
    | Or x -> String.concat " | " (List.map (fun x -> "(" ^ (printFormula elementPrinter x) ^ ")") x)

type 'a nf = 'a list list
type space = (operator M.t * coef M.t) * expr formula

let combineFormulae opAnd x y =
    match (opAnd, x, y) with
    | (true, And x, And y) -> And(y @ x)
    | (true, And x, _) -> And(y :: x)
    | (true, _, And y) -> And(y @ [ x ])
    | (true, _, _) -> And [ y ; x ]
    | (_, Or x, Or y) -> Or(y @ x)
    | (_, Or x, _) -> Or(y :: x)
    | (_, _, Or y) -> Or(y @ [ x ])
    | _ -> Or [ y ; x ]

(* This procedure sums up all terms according to the variable and move to the
   left-side of the expression. It flips greater-than operators (>, >=) to
   less-than operators (<, <=) and replaces strict inequality (<, >) with not
   strict ones (<=, >=) by doing +/- 1 on constant term. Returns the operator
   and the mapping from a variable to its coefficient. The constant term has the
   empty string as a key. *)
let normalizeExpr (op, t1, t2) =
    let addCoef sign coefs (coef, key) =
        M.add key (sign * coef +
            (if M.mem key coefs then M.find key coefs else 0)) coefs in
    let t2, sign, op =
        match op with
        | LT -> (-1, "") :: t2, 1, LTE
        | GT -> (1, "") :: t2, -1, LTE
        | GTE -> t2, -1, LTE
        | _ -> t2, 1, op in
    let coefs = M.add "" 0 M.empty in
    let coefs = List.fold_left (addCoef sign) coefs t1 in
    let coefs = List.fold_left (addCoef (-sign)) coefs t2 in
    let coefs = M.fold (fun k v coefs ->
        if k <> "" && v = 0 then M.remove k coefs else coefs) coefs coefs in
    op, coefs
