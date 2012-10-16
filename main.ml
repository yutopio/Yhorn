open Util
open Parser
open Types

let fabs x = if x < 0. then -.x else x
let tryPick f = List.fold_left (fun ret x -> if ret = None then f x else ret) None
let addDefault k v d (+) m =
    M.add k ((+) (if M.mem k m then M.find k m else d) v) m

let printExpr2 offset (op, coef) =
    print_string offset;
    let first = ref true in
    M.iter (fun v c ->
        if v = "" || c = 0 then () else (
        print_string (if c > 0 && not !first then "+" else if c = -1 then "-" else "");
        first := false;
        if (abs c) <> 1 then print_int c;
        print_string v)) coef;
    if !first then print_string "0";
    print_string (string_of_operator op);
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
let coefOp op = M.fold (fun k v -> addDefault k v 0 op)
let invert = M.map (fun v -> -v)

(* Try to calculate an interpolant from given expressions. All expressions are
   to be represented as (consider : bool, (operator, coefficients : int M.t)).
   The first bool represents if the expression should be considered as the first
   logical group (in other words, to be considered when making an interpolant).
   Other parameter represents the expression. The operator should be either LTE
   or EQ. Any other are considered as LTE. *)
let getSpace exprs =
    let exprs = (true, (LTE, M.add "" (-1) M.empty)) :: exprs in

    (* DEBUG: Debug output *)
    print_endline "\nExpressions:";
    List.iter (fun (f, e) -> if f then printExpr2 "\t" e) exprs;
    print_endline "    --------------------";
    List.iter (fun (f, e) -> if not f then printExpr2 "\t" e) exprs;

    (* Build linear constraints for an SMT solver *)
    let m, constrs, (a, b), ipLte =
        List.fold_left (fun (m, constrs, (a, b), ipLte) (c, (op, coef)) ->
            let pi = "p" ^ (string_of_int (new_id ())) in
            let m = M.fold (fun k v -> addDefault
                k (pi, v) M.empty (fun m (k, v) -> M.add k v m)) coef m in
            let constrs = match op with
                | EQ -> constrs
                | LTE -> (LTE, M.add pi (-1) M.empty) :: constrs
                | _ -> assert false in
            let (a, b) = if c then (pi :: a), b else a, (pi :: b) in
            let ipLte = ipLte || (c && op = LTE) in
            (m, constrs, (a, b), ipLte))
        (M.empty, [], ([], []), false) exprs in

    let op = (if ipLte then LTE else EQ) in
    let coef = M.map (M.filter (fun k _ -> List.mem k a)) m in
    let constrs = ((if constrs = [] then NEQ else GT), M.find "" m) ::
        (M.fold (fun k v -> (@) (if k = "" then [] else [ (EQ, v) ])) m constrs) in
    (op, coef), constrs, [(a @ b)]

let getInterpolant ((op, expr), coef, zero) =
    let ret = try
        let sol = Z3py.integer_programming (coef, zero) in

        (* Construct one interpolant *)
        let expr = M.map (fun v -> M.fold (fun k v -> (+) ((M.find k sol) * v)) v 0) expr in
        let m = op, expr in

        (* DEBUG: Debug output *)
        print_endline "\nInterpolant:";
        printExpr2 "\t" m;

        Some m
    with _ -> None in

    print_endline "\n==========";
    ret

let solve a b =
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

    let tryGetInterpolant2 x =
        let sp = getSpace x in
        match getInterpolant sp with None -> None | Some _ -> Some sp in
    let tryGetInterpolant coefProc exprs = tryPick (fun (consider, (_, coef)) ->
        let sp = getSpace ((consider, (LTE, coefProc coef)) :: exprs) in
        match getInterpolant sp with None -> None | Some _ -> Some sp) in

    let eqAeqB _ =
        let eqs = eqA @ eqB in
        tryPick exec [
            (fun _ -> tryGetInterpolant2 eqs);
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
        tryPick (fun x -> tryGetInterpolant2 (x @ exprs)) (directProduct neqs) in

    tryPick exec [
        (if leqA <> 0 then (if leqB <> 0 then eqAeqB else eqAneqB) else neqAeqB);
        all]

let intersectSpace ((op1, coef1), constrs1, zero1) ((op2, coef2), constrs2, zero2) =
    let x1 = M.fold (fun k v r -> k :: r) coef1 [] in
    let x2 = M.fold (fun k v r -> k :: r) coef2 [] in
    let vars = distinct (x1 @ x2) in

    let constrs3 = List.fold_left (fun ret k ->
        let v1 = if M.mem k coef1 then M.find k coef1 else M.empty in
        let v2 = if M.mem k coef2 then M.find k coef2 else M.empty in
        let v = coefOp (-) v1 v2 in (EQ, v) :: ret) [] vars in
    let constrs = constrs1 @ constrs2 @ constrs3 in

    let op = match op1, op2 with
        | EQ, _
        | _, EQ -> EQ
        | _ -> LTE in

    ((op, coef1), constrs, zero1 @ zero2)

let formulae = inputUnit Lexer.token (Lexing.from_channel stdin)
let groups = directProduct (List.map convertToDNF formulae)
let a = List.map (fun x -> solve (List.hd x) (List.nth x 1)) groups
let a = List.filter (function None -> false | _ -> true) a
let a = List.map (function (Some x) -> x) a
let combine = reduce intersectSpace a
let _ = print_endline "\nIntersection of interpolant spaces:"
let _ = getInterpolant combine
