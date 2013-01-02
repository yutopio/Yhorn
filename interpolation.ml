open Util
open Types

(** [any] denotes the interpolant space x=0 where x can be anything. Equivalent
    of (0=0 | 0=1). *)
let any = Expr ((M.empty, M.add "" (M.add "x" 1 M.empty) M.empty),
    Expr (EQ, M.empty))

(** [bot] denotes the interpolant space x=0 where x is not equal to 0.
    Equivalent of 0=1. *)
let bot = Expr ((M.empty, M.add "" (M.add "x" 1 M.empty) M.empty),
    Expr (NEQ, M.add "x" 1 M.empty))

(** [top] denotes the interpolant space 0=0. *)
let top = Expr ((M.empty, M.empty), Expr (EQ, M.empty))

(* Try to calculate an interpolant from given expressions. All expressions are
   to be represented as (consider : bool, (operator, coefficients : int M.t)).
   The first bool represents if the expression should be considered as the first
   logical group (in other words, to be considered when making an interpolant).
   Other parameter represents the expression. The operator should be either LTE
   or EQ. Any other are considered as LTE. *)
let getSpace exprs =
    (* Add 0 <= 1 constraint for completeness. *)
    let exprs = (true, (LTE, M.add "" (-1) M.empty)) :: exprs in

    (* DEBUG: Debug output *)
    print_endline "\nExpressions:";
    List.iter (fun (f, e) -> if f then print_endline ("\t" ^ (printExpr e))) exprs;
    print_endline "    --------------------";
    List.iter (fun (f, e) -> if not f then print_endline ("\t" ^ (printExpr e))) exprs;
    (* DEBUG: Following code snippets also shows expression numbers
    print_endline "\nExpressions:";
    let _ = List.fold_left (fun i (f, e) -> if f then print_endline (
        (string_of_int i) ^ "\t" ^ (printExpr e)); i + 1) 0 exprs in
    print_endline "    --------------------";
    let _ = List.fold_left (fun i (f, e) -> if not f then print_endline (
        (string_of_int i) ^ "\t" ^ (printExpr e)); i + 1) 0 exprs in *)

    (* Build the coefficient mapping for the first, and at the same time, check
       the operator of each expression. *)
    let m, constrs, (a, b), op =
        List.fold_left (fun (m, constrs, (a, b), ipOp) (c, (op, coef)) ->
            let id = string_of_int (new_id ()) in
            let pi = "p" ^ id in

            (* DEBUG: *)
            print_endline (id ^ "\t" ^ (printExpr (op, coef)));

            (* Building an coefficient mapping in terms of variables *)
            (M.fold (fun k v -> M.addDefault
                M.empty (fun m (k, v) -> M.add k v m) k (pi, v)) coef m),

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

let assignParameters assign (op, expr) =
  (M.fold (fun k v o -> if v <> 0 && M.findDefault EQ k op = LTE then
      (assert (v > 0); LTE) else o) assign EQ),
  (M.map (fun v -> M.fold (fun k v -> (+) ((
    M.findDefault 1 k assign) * v)) v 0) expr)

let rec getInterpolant sp =
    match sp with
    | Expr (pexpr, constraints) -> (
        (* DEBUG: Z3 integer programming constraint.
        print_endline (printFormula printExpr constraints); *)

        match Z3interface.integer_programming constraints with
        | Some sol ->
            (* DEBUG: Dump Z3 solution.
            print_endline ("Z3 solution: [" ^ (String.concat ", " (
            M.fold (fun k v l -> (k ^ "=" ^ (string_of_int v)) :: l) sol [])) ^ "]"); *)

            (* Construct one interpolant *)
            Some(Expr (assignParameters sol pexpr))
        | None -> None)
    | And sps -> getInterpolantList true sps
    | Or sps -> getInterpolantList false sps
and getInterpolantList opAnd sps =
    (* If the space is expressed by the union of spaces, take one interpolant from each space *)
    try
        let is = List.map (fun x ->
            match getInterpolant x with
            | Some x -> x
            | None -> raise Not_found) sps in
        Some (if opAnd then And is else Or is)
    with Not_found -> None

(* DEBUG: Uncomment following lines to dump intermediate interpolants
let getInterpolant sp =
    let ret = getInterpolant sp in
    (match ret with
      | Some x -> print_endline (printFormula printExpr x)
      | None -> print_endline "none");
    ret *)

let generatePexprMergeConstr (op1, coef1) (op2, coef2) =
  (* Consider all variables are present in both *)
  let vars = [] |>
    M.fold (fun k v r -> k :: r) coef1 |>
    M.fold (fun k v r -> k :: r) coef2 |>
    distinct in

  (* Coefficients of both interpolants must be the same *)
  let (c3, c4) = List.fold_left (fun (r1, r2) k ->
    let [v1;v2] = List.map (M.findDefault M.empty k) [coef1;coef2] in
    (Expr(EQ, v1 ++ v2) :: r1),
    (Expr(EQ, v1 -- v2) :: r2)) ([], []) vars in

  (* Check weight variables those for making an interpolant LTE. *)
  let f x =
    let p = M.fold (fun k v p -> if v = LTE then k :: p else p) x [] in
    let eq = List.fold_left (fun c x ->
      (Expr (EQ, M.add x 1 M.empty)) :: c) [] p in
    (p, eq) in
  let (p1lte, i1eq), (p2lte, i2eq) = (f op1), (f op2) in

  let [c3;c4;i1eq;i2eq] = List.map (reduce (&&&)) [c3;c4;i1eq;i2eq] in

  (* Constraint for making both interpolant the same operator. *)
  match p1lte, p2lte with
    | [], [] -> c3 ||| c4
    | _, [] -> (c3 ||| c4) &&& i1eq
    | [], _ -> (c3 ||| c4) &&& i2eq
    | _ -> (i1eq <=> i2eq) &&& (i1eq ==> (c3 ||| c4)) &&& ((!!! i1eq) ==> c4)

let rec mergeSpace opAnd sp1 sp2 =
    let mergeSpSp ((op1, coef1), c1) ((op2, coef2), c2) =
        let c5 = generatePexprMergeConstr (op1, coef1) (op2, coef2) in
        let sp = ((M.fold M.add op1 op2), coef1), (c1 &&& c2 &&& c5) in
        match getInterpolant (Expr sp) with
        | Some _ -> Expr sp
        | None ->
            if opAnd then
                (* (* If failed to merge space for And, there is no interpolant. *)
                Expr ((M.empty, M.empty), Expr(EQ, M.add "" 1 M.empty)) *)
                And [ sp1; sp2]
            else Or [ sp1; sp2 ] in

    let mergeSpSps sp sps spsAnd =
        (* Try to take simple intersection between each space and one. When
           successful, newly created spaces will be concatenated. Otherwise,
           just add one space into the list. *)
        try
            let sps = List.map (fun sp1 ->
                match (mergeSpace opAnd sp sp1), opAnd with
                | Expr x, _ -> Expr x
                | And _, true
                | Or _, false -> raise Not_found
                | _ -> assert false) sps in
            if spsAnd then And sps else Or sps
        with Not_found -> (
            match opAnd, spsAnd with
            | true, true -> And (sp :: sps)
            | true, false -> And [ sp; Or sps ]
            | false, true -> Or [ sp; And sps ]
            | false, false -> Or (sp :: sps)) in

    match sp1, sp2, opAnd with
    | Expr e1, Expr e2, _ -> mergeSpSp e1 e2
    | And sps, Expr e, _
    | Expr e, And sps, _ -> mergeSpSps (Expr e) sps true
    | And sps1, And sps2, true -> And (sps1 @ sps2)
    | Or sps, Expr e, _
    | Expr e, Or sps, _ -> mergeSpSps (Expr e) sps false
    | Or sps1, Or sps2, false -> Or (sps1 @ sps2)
    | And sps_a, Or sps_o, true
    | Or sps_o, And sps_a, true -> And ((Or sps_o) :: sps_a)
    | And sps_a, Or sps_o, false
    | Or sps_o, And sps_a, false -> Or ((And sps_a) :: sps_o)
    | _, _, true -> And [ sp1; sp2 ]
    | _, _, false -> Or [ sp1; sp2 ]

let laSolve a b =
    let filter op = List.filter (fun (x, _) -> x = op) in
    let addFlag op exprs consider = List.map (fun x -> (consider, x)) (filter op exprs) in
    let proc op exprs consider = let t = addFlag op exprs consider in (t, List.length t) in
    let exec = fun x -> x () in

    (* Extract all equations and not-equal inequations *)
    let eqA, leqA = proc EQ a true in
    let neqA, lneqA = proc NEQ a true in
    let eqB, leqB = proc EQ b false in
    let neqB, lneqB = proc NEQ b false in
    let plus x = M.addDefault 0 (+) "" 1 x in
    let minus x = M.add "" (1 - (M.findDefault 0 "" x)) (~-- x) in

    let tryGetInterpolant opAnd exprs = tryPick (fun (consider, (_, coef)) ->
        (* DEBUG: List.rev is for ease of inspection *)
        let sp1 = Expr(getSpace (List.rev ((consider, (LTE, plus coef)) :: exprs))) in
        match getInterpolant sp1 with None -> None | Some _ ->
        let sp2 = Expr(getSpace (List.rev ((consider, (LTE, minus coef)) :: exprs))) in
        match getInterpolant sp2 with None -> None | Some _ ->
        Some(mergeSpace opAnd sp1 sp2)) in

    let none _ = None in

    let eqAeqB _ =
        let eqs = eqA @ eqB in
        tryPick exec [
            (fun _ -> tryGetInterpolant false eqs neqA);
            (fun _ -> tryGetInterpolant true eqs neqB) ] in
    let eqAneqB _ = tryGetInterpolant true eqA neqB in
    let neqAeqB _ = tryGetInterpolant false eqB neqA in

    let eqAll _ =
        let sp = Expr(getSpace ((List.map (fun x -> true, x) a) @ (List.map (fun x -> false, x) b))) in
        match getInterpolant sp with None -> None | Some _ -> Some sp in

    let all _ =
        (* Gather all expressions of LTE with consideration flag. *)
        let exprs = (addFlag LTE a true) @ (addFlag LTE b false) @ (eqA @ eqB) in

        (* Split not-equal inequations into disjunction of two expressions and
           choose either as for each inequations. *)
        let neqExpand = List.map (fun (c, (_, coef)) ->
            [ (c, (LTE, plus coef)) ; (c, (LTE, minus coef)) ]) in
        let neqAs = directProduct (neqExpand neqA) in
        let neqBs = directProduct (neqExpand neqB) in

        (* Try to get interpolant *)
        try
            Some (
            reduce (mergeSpace true) (List.map (fun b ->
            reduce (mergeSpace false) (List.map (fun a ->
                let sp = Expr (getSpace (exprs @ a @ b)) in
                match getInterpolant sp with
                | Some _ -> sp
                | None -> raise Not_found) neqAs)) neqBs))
        with Not_found -> None in

    tryPick exec [
        (if leqA <> 0 then (if leqB <> 0 then eqAeqB else eqAneqB) else neqAeqB);
        (if lneqA + lneqB = 0 then eqAll else none);
        all]

let interpolate formulae = try (
    match List.map (
      mapFormula normalizeExpr |-
      splitNegation |-
      convertToNF false) formulae with
    | [a_s; b_s] -> (
        try
            (* Remove contradictory conjunctions. *)
            let removeContradiction l =
                List.rev (List.fold_left (fun l x -> match laSolve x [] with
                  | Some _ -> l
                  | None -> x :: l) [] l) in
            let a_s = removeContradiction a_s in
            let b_s = removeContradiction b_s in

            Some (match a_s, b_s with
            | [], [] -> any
            | [], _ -> bot
            | _, [] -> top
            | _, _ ->

            (* Calculate the interpolant space between each conjunctions from A
               and B. *)
            let spaces = List.map (fun b -> List.map (fun a ->
                match laSolve a b with
                | Some x -> x
                | None -> raise Not_found) a_s) b_s in

(* DEBUG: Copied from util.ml in VHorn *)
let rec transpose xss = (
  if List.for_all (fun xs -> xs = []) xss then
    []
  else
    let xs, xss =
      List.split
        (List.map (function x::xs -> x, xs | _ -> assert false ) xss)
    in
    xs::transpose xss) in
(*************************************************)

            let cnf = reduce (mergeSpace true) (
                List.map (reduce (mergeSpace false)) spaces) in
            let dnf = reduce (mergeSpace false) (
                List.map (reduce (mergeSpace true)) (transpose spaces)) in
            if countFormula cnf > countFormula dnf then dnf else cnf)
        with Not_found -> None)
    | _ -> assert false (* TODO: NYI *)

    ) with e ->
        print_endline ("Yint: Unhandled exception (" ^
            (Printexc.to_string e) ^
            ")");
        assert false