
open Buffer
open Map
open Set
open Util

module MyString = struct
  type t = string
  let compare = compare
end

module M = MapEx.Make(MyString)
module S = Set.Make(MyString)

type operator =
    | EQ
    | NEQ
    | LT
    | LTE
    | GT
    | GTE

let negateOp = function
    | EQ -> NEQ
    | NEQ -> EQ
    | LT -> GTE
    | LTE -> GT
    | GT -> LTE
    | GTE -> LT

let string_of_operator = function
    | EQ -> "=="
    | NEQ -> "!="
    | LT -> "<"
    | LTE -> "<="
    | GT -> ">"
    | GTE -> ">="

type coef = int M.t

let coefOp op d = M.fold (fun k v -> M.addDefault k v d op)
let (++) = coefOp (+) 0
let (--) x y = coefOp (-) 0 y x (* Note that the operands need to be reversed. *)
let (~--) = M.map (fun v -> -v)

type expr = operator * coef
type pvar = string * string list

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

(** Flips greater-than operators (>, >=) to less-than operators (<, <=) and
    replaces strict inequality (<, >) with not strict ones (<=, >=) by adding 1
    on constant term. Any variables with 0-weight are eliminated. Returns the
    operator and the coefficient mapping. *)
let normalizeExpr (op, coef) =
    let op, coef =
        match op with
        | LT -> LTE, (M.addDefault "" 1 0 (+) coef)
        | GT -> LTE, (M.addDefault "" 1 0 (+) (~-- coef))
        | GTE -> LTE, (~-- coef)
        | _ -> op, coef in
    op, (M.filter (fun _ v -> v <> 0) coef)

let negateExpr (op, coef) = (negateOp op, coef)

let rec renameInternal m k =
  if not (M.mem k !m) then
    m := M.add k ("$" ^ string_of_int (new_id ())) !m;
  M.find k !m
and renameExpr m (op, coef) =
  (op, M.fold (fun k -> M.add (if k = "" then "" else renameInternal m k)) coef M.empty)
and renameList m = List.map (renameInternal m)

let printPvar (name, params) =
    name ^ "(" ^ String.concat "," params ^ ")"

type 'a formula =
    | Expr of 'a
    | And of 'a formula list
    | Or of 'a formula list

let rec printFormula eltPrinter x =
    let ret = match x with
    | Expr x -> `A x
    | And x -> `B(x, " & ")
    | Or x -> `B(x, " | ") in

    match ret with
    | `A x -> eltPrinter x
    | `B(x, y) -> String.concat y (List.map (
        fun x -> "(" ^ (printFormula eltPrinter x) ^ ")") x)

let combineFormulae opAnd x y =
    match (opAnd, x, y) with
    | (true, And x, And y) -> And (y @ x)
    | (true, And x, _) -> And (y :: x)
    | (true, _, And y) -> And (y @ [ x ])
    | (true, _, _) -> And [ y ; x ]
    | (_, Or x, Or y) -> Or (y @ x)
    | (_, Or x, _) -> Or (y :: x)
    | (_, _, Or y) -> Or (y @ [ x ])
    | _ -> Or [ y ; x ]
let (&&&) : expr formula -> expr formula -> expr formula = combineFormulae true
let (|||) : expr formula -> expr formula -> expr formula = combineFormulae false

let rec mapFormula f = function
    | And x -> And (List.map (mapFormula f) x)
    | Or x -> Or (List.map (mapFormula f) x)
    | Expr e -> Expr (f e)

let (!!!) : expr formula -> expr formula = mapFormula negateExpr

let rec countFormula = function
    | And x
    | Or x -> List.fold_left (+) 0 (List.map countFormula x)
    | Expr _ -> 1

type hornTerm =
    | LinearExpr of expr formula
    | PredVar of pvar
type horn = hornTerm list * hornTerm

let printHornTerm = function
    | LinearExpr e -> printFormula printExpr e
    | PredVar p -> printPvar p

(** Normal form of element *)
type 'a nf = 'a list list

let convertToNF cnf formulae =
    let rec internal formulae ret =
        match formulae with
        | [] -> List.rev ret
        | x :: l ->
            let ret = match x with
                | Expr x -> [ x ] :: ret
                | And x | Or x -> (directProduct (internal x [])) @ ret in
            internal l ret in
    match cnf, formulae with
    | true, And x
    | false, Or x -> internal x []
    | _ -> internal [ formulae ] []

(** Solution space of interpolation *)
type pexpr = operator M.t * coef M.t
let (+++) (o1, c1) (o2, c2) =
  (M.simpleMerge o1 o2),
  (coefOp M.simpleMerge M.empty c1 c2)

type constr = expr formula
type space = pexpr * constr

type hornSolSpace = (string list * pexpr formula) M.t * constr
type hornSol = (string list * expr formula) M.t
