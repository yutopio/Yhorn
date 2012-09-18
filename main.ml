open Glpk
open Parser
open Types

let fabs x = if x < 0. then -.x else x
let tryPick f = List.fold_left (fun ret x -> if ret = None then f x else ret) None

let printExpr2 offset (op, coef) =
    print_string offset;
    let first = ref true in
    M.iter (fun v c ->
        if v = "" || c = 0 then () else (
        print_string (if c > 0 & not (!first) then "+" else if c = -1 then "-" else "");
        if (abs c) <> 1 then print_int c;
        print_string v);
        first := false) coef;
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

let getInterpolant exprs =
    (* DEBUG: Debug output *)
    print_endline "Expressions:";
    List.iter (fun (f, e) -> if f then printExpr2 "\t" e) exprs;
    print_endline "    --------------------";
    List.iter (fun (f, e) -> if not f then printExpr2 "\t" e) exprs;
    print_endline "\n";

    let exprs = listToArray exprs in
    let len = Array.length exprs in

    (* Assign indices for all variables *)
    let vars = ref (-1) in
    let varIDs = Array.fold_left (fun m (_, (_, coefs)) ->
        M.fold (fun k _ m ->
            if not (M.mem k m || k = "") then
                (incr vars; M.add k !vars m) else m) coefs m) M.empty exprs in
    let vars = incr vars; !vars in

    (* Build linear programming problem for OCaml Glpk *)
    (* TODO: Use of SMT solvers as an alternative method *)
    let zcoefs = Array.map (fun (_, coef) -> 0.) exprs in
    let constrs = Array.make_matrix (vars + 2) len 0. in
    let pbounds = Array.create (vars + 2) (0., 0.) in
    let xbounds = Array.create len (0., infinity) in

    (* Coefficient part of the constraints: must be equal to zero in pbounds at
       corresponding rows *)
    Array.iteri (fun i (_, (_, coef)) -> M.iter (fun k v ->
        if k <> "" then constrs.(M.find k varIDs).(i) <- float_of_int v) coef) exprs;

    (* Constant part should satisfy certain condition according to the given
       expressions *)
    constrs.(vars) <- (Array.map (fun (_ ,(_, coef)) -> -.(float_of_int (M.find "" coef))) exprs);
    pbounds.(vars) <- (-.infinity, 1e-5 (* epsilon *));

    (* The primal solution must not be trivial: must have more than 1 in total
       of all elements *)
    constrs.(vars + 1) <- (Array.create len 1.);
    pbounds.(vars + 1) <- (1., infinity);

    try
        let lp = make_problem Minimize zcoefs constrs pbounds xbounds in
        set_message_level lp 0;
        scale_problem lp;
        use_presolver lp true;
        simplex lp;

        (* DEBUG: Debug output *)
        let prim = get_col_primals lp in
        let prim = Array.map (fun x -> int_of_float(x *. 72.)) prim in
        print_endline "\n\nLP solution:";
        (* TODO: Want to have an integer vector *)
        printVector "\t" prim;

        (* Calculate one interpolant *)
        let i = ref 0 in
        let m = Array.fold_left (fun (f1, m) (consider, (f2, coefs)) ->
            if not consider then (f1, m) else
            LTE (* FIXME: should evaluate operators of each expression *),
            let w = prim.(!i) in incr i;
            if w = 0 then m else
            M.fold (fun x v m ->
                let v = (if M.mem x m then M.find x m else 0) + v * w in
                M.add x v m) coefs m) (EQ, M.empty) exprs in

        (* DEBUG: Debug output *)
        print_endline "\n\nInterpolant:";
        printExpr2 "\t" m;

        print_endline "\n==========";
        Some m
    with _ -> None

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

let test = "x = z & y = z ; x >= w & y + 1 <= w"

let formulae = inputUnit Lexer.token (Lexing.from_string test)
let groups = directProduct (List.map convertToDNF formulae)
let a = List.map (fun x -> prelude (List.hd x) (List.nth x 1)) groups
