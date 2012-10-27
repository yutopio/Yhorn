open Util
open Parser
open Types

let addDefault k v d (+) m =
    M.add k ((+) (if M.mem k m then M.find k m else d) v) m

let convertToDNF formulae =
    let rec internal formulae ret =
        match formulae with
        | [] -> List.rev ret
        | x :: l ->
            let ret = match x with
                | Expr x -> [ x ] :: ret
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

    (* Build the coefficient mapping for the first, and at the same time, check
       the operator of each expression. *)
    let m, constrs, (a, b), op =
        List.fold_left (fun (m, constrs, (a, b), ipOp) (c, (op, coef)) ->
            let pi = "p" ^ (string_of_int (new_id ())) in

            (* Building an coefficient mapping in terms of variables *)
            (M.fold (fun k v -> addDefault
                k (pi, v) M.empty (fun m (k, v) -> M.add k v m)) coef m),

            (* If the expression is an inequality, its weight should be
               positive *)
            (match op with
                | EQ -> constrs
                | LTE -> Expr(GTE, M.add pi 1 M.empty) :: constrs
                | _ -> assert false),

            (* To build the coefficient mapping for an interpolant, the variable
               name for the weight of each expression should be memorized *)
            (if c then (pi :: a), b else a, (pi :: b)),

            (* The flag to note that the interpolant should be LTE or EQ *)
            (if c then M.add pi op ipOp else ipOp))
        (M.empty, [], ([], []), M.empty) exprs in

    (* The interpolant will be a sum among some expressions *)
    (op, M.map (M.filter (fun k _ -> List.mem k a)) m),

    (* In constraints, all variables' coefficients must be equals to zero under
       given weights to each expression. As for the constants, if all expression
       were equalities, the sum of them must be not equal (NEQ) to zero to make
       inconsistency. Otherwise, i.e., LTE inequalities involved, the sum must
       be greater than zero. *)
    And(List.rev (  (* DEBUG: rev *)
        M.fold (fun k v -> (@) [ Expr((if k = "" then
            (if constrs = [] then NEQ else GT) else EQ), v) ]) m constrs))

let rec getInterpolant sp =
    match sp with
    | Expr ((op, expr), constraints) -> (
        try
            let sol = Z3py.integer_programming constraints in

            (* Construct one interpolant *)
            let expr = M.map (fun v -> M.fold (fun k v -> (+) ((M.find k sol) * v)) v 0) expr in
            let op = M.fold (fun k v o -> if v <> 0 && M.mem k op && M.find k op = LTE then
                (assert (v > 0); LTE) else o) sol EQ in

            let m = op, expr in

            Some (Expr m)
        with _ -> None)
    | And sps ->
        (* If the space is expressed by the union of spaces, take one interpolant from each space *)
        Some (Or (List.map (fun x ->
            match getInterpolant x with
            | Some x -> x
            | None -> assert false) sps))

let rec intersectSpace sp1 sp2 =
    match sp1, sp2 with
    | Expr ((op1, coef1), And c1),
      Expr ((op2, coef2), And c2) -> (

        (* Consider all variables are present in both *)
        let x1 = M.fold (fun k v r -> k :: r) coef1 [] in
        let x2 = M.fold (fun k v r -> k :: r) coef2 [] in
        let vars = distinct (x1 @ x2) in

        (* Coefficients of both interpolants must be the same *)
        let (c3, c4) = List.fold_left (fun (r1, r2) k ->
            let v1 = if M.mem k coef1 then M.find k coef1 else M.empty in
            let v2 = if M.mem k coef2 then M.find k coef2 else M.empty in
            (let v = coefOp (+) v1 v2 in Expr(EQ, v) :: r1),
            (let v = coefOp (-) v1 v2 in Expr(EQ, v) :: r2)) ([], []) vars in

        (* DEBUG: rev is for ease of inspection *)
        let c3, c4 = (List.rev c3), (List.rev c4) in

        (* Check weight variables those for making an interpolant LTE rather
           than EQ. Note i1eq = ~i1lte and i2eq = ~i2lte. *)
        let f x =
            let p = ref [] in
            M.iter (fun k v -> if v = LTE then p := k :: !p) x;
            let eq, neq = List.fold_left (fun (c1, c2) x ->
                ((Expr (EQ, M.add x 1 M.empty)) :: c1),
                ((Expr (NEQ, M.add x 1 M.empty)) :: c2)) ([], []) !p in
            (!p, eq, neq) in
        let (p1lte, i1eq, i1lte), (p2lte, i2eq, i2lte) = (f op1), (f op2) in

        (* Constraint for making both interpolant the same operator. *)
        let c5 = match p1lte, p2lte with
            | [], [] -> [ Or [ And c3; And c4 ] ]
            | _, [] -> (Or [ And c3; And c4 ]) :: i1eq
            | [], _ -> (Or [ And c3; And c4 ]) :: i2eq
            | _, _ -> [ Or ((And i2eq) :: i1lte); Or ((And i1eq) :: i2lte);
                Or ([ And c3; And c4 ] @ i1lte); Or [ And i1eq; And c4 ] ] in

          let sp = ((M.fold M.add op1 op2), coef1), (And (c1 @ c2 @ c5)) in
        match getInterpolant (Expr sp) with
        | Some _ -> Expr sp
        | None ->
        And [ sp1; sp2 ])

    | And sps, Expr e
    | Expr e, And sps -> (

        (* Try to take simple intersection between each space and one. When
           successful, newly created spaces will be concatenated. Otherwise,
           just add one space into the list. *)
        try
            let sps = List.map (fun sp ->
                match intersectSpace (Expr e) sp with
                | Expr x -> Expr x
                | And _ -> raise Not_found
                | _ -> assert false) sps in
            And sps
        with Not_found -> And ((Expr e) :: sps)

    )

    | And sps1, And sps2 -> And (sps1 @ sps2)

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

    let tryGetInterpolant exprs = tryPick (fun (consider, (_, coef)) ->
        (* DEBUG: List.rev is for ease of inspection *)
        let sp1 = Expr(getSpace (List.rev ((consider, (LTE, plus coef)) :: exprs))) in
        match getInterpolant sp1 with None -> None | Some _ ->
        let sp2 = Expr(getSpace (List.rev ((consider, (LTE, minus coef)) :: exprs))) in
        match getInterpolant sp2 with None -> None | Some _ ->
        Some(intersectSpace sp1 sp2)) in

    let eqAeqB _ =
        let eqs = eqA @ eqB in
        tryPick exec [
            (fun _ -> tryGetInterpolant eqs neqA);
            (fun _ -> tryGetInterpolant eqs neqB) ] in
    let eqAneqB _ = tryGetInterpolant eqA neqB in
    let neqAeqB _ = tryGetInterpolant eqB neqA in

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
        tryPick (fun x ->
            let sp = Expr(getSpace (x @ exprs)) in
            match getInterpolant sp with None -> None | Some _ -> Some(sp)
        ) (directProduct neqs) in

    tryPick exec [
        (if leqA <> 0 then (if leqB <> 0 then eqAeqB else eqAneqB) else neqAeqB);
        (if lneqA + lneqB = 0 then fun () -> (
            let sp = Expr(getSpace ((List.map (fun x -> true, x) a) @ (List.map (fun x -> false, x) b))) in
            match getInterpolant sp with None -> None | Some _ -> Some sp) else fun () -> None);
        all]

let formulae = inputUnit Lexer.token (Lexing.from_channel stdin)
let groups = directProduct (List.map convertToDNF formulae)
let a = List.map (fun x -> solve (List.hd x) (List.nth x 1)) groups
let a = List.filter (function None -> false | _ -> true) a
let a = List.map (function (Some x) -> x) a

let t =
    print_endline "\nSolution:";
    let combine = reduce intersectSpace a in
    let sol = match getInterpolant combine with
        | Some t -> printFormula printExpr t
        | _ -> "No solution" in
    print_endline ("\t" ^ sol)
