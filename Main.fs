module Main

open System
open System.Collections.Generic
open System.Linq
open System.Text
open Microsoft.FSharp.Collections
open Parser
open Types

(* Mock *)
let Minimize = ()
let make_problem _ _ _ _ _ = ()
let set_message_level _ _ = ()
let scale_problem _ = ()
let use_presolver _ _ = ()
let simplex _ = ()
let get_col_primals _ = Array.create 10 1

let mapIter f (dic:Dictionary<_,_>) =
    Array.iter (fun k -> f k dic.[k]) (dic.Keys.ToArray())
let float_of_int (x:int) = Double.Parse(x.ToString())
let abs x = if x < 0. then -x else x

let printExpr2 (offset:string) ((op, coef):expr2) =
    let ret = new StringBuilder() in
    let first = ref true in
    mapIter (fun v (c:int) ->
        if v = "" then () else
        let cc = Math.Abs(c) in
        if cc = 0 then () else
        let format = (if c < 0 then "-" else if not (!first) then "+" else "") + (if cc <> 1 then "{0}" else "") + "{1}" in
        (ret.AppendFormat(format, cc, v)); first := false) coef;
    ret.Append(match op with
        | EQ -> " = "
        | NEQ -> " <> "
        | LT -> " < "
        | LTE -> " <= "
        | GT -> " > "
        | GTE -> " >= ");
    ret.Append(-(coef.[""]));
    Console.WriteLine(offset + ret.ToString())

let printMatrix (offset:string) =
    Array.iter (fun x ->
        Console.Write(offset);
        Array.iter (fun (x:int) -> Console.Write("{0}\t", x)) x;
        Console.WriteLine())
let printVector (offset:string) (x:int []) =
    let elems = x.Select(fun (x:int) -> x.ToString()).ToArray() in
    Console.WriteLine("{0}( {1} )", offset, String.Join("\t", elems))

let directProduct input =
    let ret = ref [] in
    let rec inner current = function
        | [] -> ret := current :: !ret
        | x :: rest -> List.iter (fun x -> inner (current @ [x]) rest) x in
    inner [] input; !ret

// This procedure sums up all terms according to the variable and move to the
// left-side of the expression. It flips greater-than operators (>, >=) to
// less-than operators (<, <=) and replaces strict inequality (<, >) with not
// strict ones (<=, >=) by doing +/- 1 on constant term. Returns the operator
// and the mapping from a variable to its coefficient. The constant term has the
// empty string as a key.
let normalizeExpr (op, t1, t2) =
    let coefs = new coef() in
    let addCoef sign (coef, key) =
        coefs.[key] <- sign * coef +
            if coefs.ContainsKey(key) then coefs.[key] else 0 in
    let t2, sign, op =
        match op with
        | LT -> (-1, "") :: t2, 1, LTE
        | GT -> (1, "") :: t2, -1, LTE
        | GTE -> t2, -1, LTE
        | _ -> t2, 1, op
    coefs.Add("", 0);
    List.iter (addCoef sign) t1;
    List.iter (addCoef (-sign)) t2;
    mapIter (fun k v -> if k <> "" & v = 0 then coefs.Remove(k); ()) coefs;
    op, coefs

let convertToDNF formulae =
    let rec Internal formulae ret =
        match formulae with
        | [] -> List.rev ret
        | x :: l ->
            let ret = match x with
                | Expr x -> [ normalizeExpr x ] :: ret
                | And x | Or x -> (directProduct (Internal x [])) @ ret in
            Internal l ret in
    match formulae with
    | Or x -> Internal x []
    | _ -> Internal [ formulae ] []

// Copies the given mapping with sign of every coefficient reversed.
let invert (coefs:coef) =
    let r = new coef(coefs) in
    mapIter (fun k v -> r.[k] <- (-v)) r; r
let copy (coefs:coef) = new coef(coefs)

let getInterpolant (exprs:(bool * expr2) list) =
    (* DEBUG: Debug output *)
    Console.WriteLine("Expressions:");
    List.iter (fun (f, e) -> if f then printExpr2 "\t" e) exprs;
    Console.WriteLine("    --------------------");
    List.iter (fun (f, e) -> if not f then printExpr2 "\t" e) exprs;
    Console.WriteLine();

    let exprs = List.toArray exprs in
    let len = Array.length exprs in

    (* Assign indices for all variables *)
    let vars = ref (-1) in
    let varIDs = new Dictionary<string, int>() in
    Array.iter (fun (_, (_, coefs)) ->
        mapIter (fun k _ ->
            if not (varIDs.ContainsKey(k) || k = "") then
                (incr vars; varIDs.Add(k, !vars))) coefs) exprs;
    let vars = incr vars; !vars in

    (* Build linear programming problem for OCaml Glpk *)
    (* TODO: Use of SMT solvers as an alternative method *)
    let zcoefs = Array.map (fun _ -> 0.) exprs in
    let constrs = Array.create (vars + 2) (Array.create len 0.) in
    let pbounds = Array.create (vars + 2) (0., 0.) in
    let xbounds = Array.create len (0., infinity) in

    (* Coefficient part of the constraints: must be equal to zero in pbounds at
       corresponding rows *)
    Array.iteri (fun i (_, (_, coef)) -> mapIter (fun k v ->
        if k <> "" then constrs.[varIDs.[k]].[i] <- (float_of_int v)) coef) exprs;

    (* Constant part should satisfy certain condition according to the given
       expressions *)
    constrs.[vars] <- (Array.map (fun (_ ,(_, coef:coef)) -> - (float_of_int coef.[""])) exprs);
    pbounds.[vars] <- (Double.NegativeInfinity, Double.Epsilon);

    (* The primal solution must not be trivial: must have more than 1 in total
       of all elements *)
    constrs.[vars + 1] <- (Array.create len 1.);
    pbounds.[vars + 1] <- (1., infinity);

    try
        let lp = make_problem Minimize zcoefs constrs pbounds xbounds in
        set_message_level lp 0;
        scale_problem lp;
        use_presolver lp true;
        simplex lp;

        (* DEBUG: Debug output *)
        let prim = get_col_primals lp in
        Console.WriteLine("\n\nLP solution:");
        (* TODO: Want to have an integer vector *)
        printVector "\t" prim;

        (* Calculate one interpolant *)
        let i = ref 0 in
        let m = new coef() in
        let m = (Array.fold (fun f1 (consider, (f2, coefs)) ->
            if not consider then f1 else
            let w = prim.[!i] in incr i;
            if w <> 0 then
                mapIter (fun x v ->
                    let v = (if m.ContainsKey(x) then m.[x] else 0) + v * w in
                    m.[x] <- v) coefs;
            LTE (* FIXME: should evaluate operators of each expression *) ) EQ exprs), m in

        (* DEBUG: Debug output *)
        Console.WriteLine("\n\nInterpolant:");
        printExpr2 "\t" m;

        Console.WriteLine("\n==========");
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
    let plus (x:coef) = let x = copy x in x.[""] <- x.[""] + 1; x in
    let minus (x:coef) = let x = invert x in x.[""] <- x.[""] + 1; x in

    let tryGetInterpolant coefProc exprs = List.tryPick (fun (consider, (_, coef)) ->
        getInterpolant ((consider, (LTE, coefProc coef)) :: exprs)) in

    let eqAeqB _ =
        let eqs = eqA @ eqB in
        List.tryPick exec [
            fun _ -> getInterpolant eqs;
            fun _ -> tryGetInterpolant plus eqs neqA;
            fun _ -> tryGetInterpolant minus eqs neqA;
            fun _ -> tryGetInterpolant plus eqs neqB;
            fun _ -> tryGetInterpolant minus eqs neqB ] in
    let eqAneqB _ =
        List.tryPick exec [
            fun _ -> tryGetInterpolant plus eqA neqB;
            fun _ -> tryGetInterpolant minus eqA neqB ] in
    let neqAeqB _ =
        List.tryPick exec [
            fun _ -> tryGetInterpolant plus eqB neqA;
            fun _ -> tryGetInterpolant minus eqB neqA ]

    let all _ =
        (* Gather all expressions of LTE with consideration flag, and expand
           equations. *)
        let exprs = (addFlag LTE a true) @ (addFlag LTE b false) @
            List.fold (fun ret (c, (_, coefs)) ->
                (c, (LTE, coefs)) ::
                (c, (LTE, invert coefs)) :: ret) [] (eqA @ eqB) in

        (* Split not-equal inequations into disjunction of two expressions and
           choose either as for each inequations. *)
        let neqs = List.map (fun (c, (_, coef)) ->
            [ (c, (LTE, plus coef)) ; (c, (LTE, minus coef)) ]) (neqA @ neqB) in
        List.tryPick (fun x -> getInterpolant (x @ exprs)) (directProduct neqs) in

    List.tryPick exec [
        (if leqA <> 0 then (if leqB <> 0 then eqAeqB else eqAneqB) else neqAeqB);
        all]

let test = "x + y >= 2 & y - 2z <= 0 & 3x - z >= 5 ; 2x - y + 3z <= 0"

let formulae = inputUnit Lexer.token (Lexing.LexBuffer<char>.FromString(test))
let groups = directProduct (List.map convertToDNF formulae)
let a = List.map (fun (x:nf) -> prelude (x.Item 0) (x.Item 1)) groups
