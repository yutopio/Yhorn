open Glpk
open Parser
open Types
open Z3py

let fabs x = if x < 0. then -.x else x
let tryPick f = List.fold_left (fun ret x -> if ret = None then f x else ret) None

let printExpr2 offset (op, coef) =
    print_string offset;
    let first = ref true in
    M.iter (fun v c ->
        if v = "" || c = 0 then () else (
        print_string (if c > 0 & not (!first) then "+" else if c = -1 then "-" else "");
        if (abs c) <> 1 then print_int c;
        print_string v;
        first := false)) coef;
    print_string (match op with
        | EQ -> " = "
        | NEQ -> " <> "
        | LT -> " < "
        | LTE -> " <= "
        | GT -> " > "
        | GTE -> " >= ");
    print_int (-(M.find "" coef));
    print_newline ()

let printMatrix offset =
    Array.iter (fun x ->
        print_string offset;
        Array.iter (fun x -> print_int x; print_string "\t") x;
        print_newline ())

let printVector offset x =
    print_string (offset ^ "( ");
    let len = Array.length x in
    Array.iteri (fun i x ->
        print_int x;
        print_string (if i = len - 1 then "" else "\t")) x;
    print_endline ")"

let directProduct input =
    let ret = ref [] in
    let rec inner current = function
        | [] -> ret := current :: !ret
        | x :: rest -> List.iter (fun x -> inner (current @ [x]) rest) x in
    inner [] input; !ret

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

let convertToDNF formulae =
    let rec internal formulae ret =
        match formulae with
        | [] -> List.rev ret
        | x :: l ->
            let ret = match x with
                | Expr x -> [ normalizeExpr x ] :: ret
                | And x | Or x -> (directProduct (internal x [])) @ ret in
            internal l ret in
    match formulae with
    | Or x -> internal x []
    | _ -> internal [ formulae ] []

(* Copies the given mapping with sign of every coefficient reversed. *)
let invert = M.map (fun v -> -v)

let listToArray l =
    let len = List.length l in
    if len = 0 then [| |] else
    let ret = Array.make len (List.hd l) in
    let i = ref 0 in
    List.iter (fun x -> ret.(!i) <- x; incr i) l;
    ret

let arrayFold2 f x a =
    let i = ref (-1) in
    Array.fold_left (fun x -> f x (a.(incr i; !i))) x

(* Try to calculate an interpolant from given expressions. All expressions are
   to be represented as (consider : bool, (operator, coefficients : int M.t)).
   The first bool represents if the expression should be considered as the first
   logical group (in other words, to be considered when making an interpolant).
   Other parameter represents the expression. The operator should be either LTE
   or EQ. Any other are considered as LTE. *)
let getInterpolant exprs =
    (* DEBUG: Debug output *)
    print_endline "\nExpressions:";
    List.iter (fun (f, e) -> if f then printExpr2 "\t" e) exprs;
    print_endline "    --------------------";
    List.iter (fun (f, e) -> if not f then printExpr2 "\t" e) exprs;

    let exprs = listToArray exprs in
    let len = Array.length exprs in

    (* Assign indices for all variables *)
    let vars = ref (-1) in
    let varIDs = Array.fold_left (fun m (_, (_, coefs)) ->
        M.fold (fun k _ m ->
            if not (M.mem k m || k = "") then
                (incr vars; M.add k !vars m) else m) coefs m) M.empty exprs in
    let vars = incr vars; !vars in

    (* Use SMT solver to solve a linear programming problem *)
    let constrs = Array.make_matrix (vars + 1) len 0 in
    let pbounds = Array.create (vars + 1) (0, 0) in
    let xbounds = Array.create len (0, max_int) in

    (* Coefficient part of the constraints: must be equal to zero in pbounds at
       corresponding rows *)
    let eq, ineq = ref false, ref false in
    Array.iteri (fun i (_, (op, coef)) ->
        M.iter (fun k v -> if k <> "" then constrs.(M.find k varIDs).(i) <- v) coef;
        if op = EQ then (xbounds.(i) <- (min_int, max_int); eq := true) else ineq := true) exprs;

    (* Constant part should satisfy certain condition according to the given
       expressions *)
    constrs.(vars) <- (Array.map (fun (_ ,(_, coef)) -> - (M.find "" coef)) exprs);
    pbounds.(vars) <- if !ineq then (min_int, -1) else (max_int, 0);

    let ret = try
        let prim = integer_programming constrs pbounds xbounds in

        (* DEBUG: Debug output *)
        print_endline "\nLP solution:";
        printVector "\t" prim;

        (* Calculate one interpolant *)
        let i = ref 0 in
        let m = Array.fold_left (fun (op1, m) (consider, (op2, coefs)) ->
            if not consider then (op1, m) else
            (if op1 = LTE then LTE else op2),
            let w = prim.(!i) in incr i;
            if w = 0 then m else
            M.fold (fun x v m ->
                let v = (if M.mem x m then M.find x m else 0) + v * w in
                M.add x v m) coefs m) (EQ, M.empty) exprs in

        (* DEBUG: Debug output *)
        print_endline "\nInterpolant:";
        printExpr2 "\t" m;

        Some m
    with _ -> None in

    print_endline "\n==========";
    ret

let prelude a b =
    let filter op = List.filter (fun (x, _) -> x = op) in
    let addFlag op exprs consider = List.map (fun x -> (consider, x)) (filter op exprs) in
    let proc op exprs consider = let t = addFlag op exprs consider in (t, List.length t) in
    let exec = fun x -> x () in

    (* Extract all equations and not-equal inequations *)
    let eqA, leqA = proc EQ a true in
    let neqA, lneqA = proc NEQ a true in
    let eqB, leqB = proc EQ b false in
    let neqB, lneqB = proc NEQ b false in
    let plus x = M.add "" (1 + (M.find "" x)) x in
    let minus x = M.add "" (1 - (M.find "" x)) (invert x) in

    let tryGetInterpolant coefProc exprs = tryPick (fun (consider, (_, coef)) ->
        getInterpolant ((consider, (LTE, coefProc coef)) :: exprs)) in

    let eqAeqB _ =
        let eqs = eqA @ eqB in
        tryPick exec [
            (fun _ -> getInterpolant eqs);
            (fun _ -> tryGetInterpolant plus eqs neqA);
            (fun _ -> tryGetInterpolant minus eqs neqA);
            (fun _ -> tryGetInterpolant plus eqs neqB);
            (fun _ -> tryGetInterpolant minus eqs neqB) ] in
    let eqAneqB _ =
        tryPick exec [
            (fun _ -> tryGetInterpolant plus eqA neqB);
            (fun _ -> tryGetInterpolant minus eqA neqB) ] in
    let neqAeqB _ =
        tryPick exec [
            (fun _ -> tryGetInterpolant plus eqB neqA);
            (fun _ -> tryGetInterpolant minus eqB neqA) ] in

    let all _ =
        (* Gather all expressions of LTE with consideration flag, and expand
           equations. *)
        let exprs = (addFlag LTE a true) @ (addFlag LTE b false) @
            List.fold_left (fun ret (c, (_, coefs)) ->
                (c, (LTE, coefs)) ::
                (c, (LTE, invert coefs)) :: ret) [] (eqA @ eqB) in

        (* Split not-equal inequations into disjunction of two expressions and
           choose either as for each inequations. *)
        let neqs = List.map (fun (c, (_, coef)) ->
            [ (c, (LTE, plus coef)) ; (c, (LTE, minus coef)) ]) (neqA @ neqB) in
        tryPick (fun x -> getInterpolant (x @ exprs)) (directProduct neqs) in

    tryPick exec [
        (if leqA <> 0 then (if leqB <> 0 then eqAeqB else eqAneqB) else neqAeqB);
        all]

let formulae = inputUnit Lexer.token (Lexing.from_channel stdin)
let groups = directProduct (List.map convertToDNF formulae)
let a = List.map (fun x -> prelude (List.hd x) (List.nth x 1)) groups
