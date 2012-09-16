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
let get_col_primals _ = Array.create 10 1.

let mapIter f (dic:Dictionary<_,_>) =
    Array.iter (fun k -> f k dic.[k]) (dic.Keys.ToArray())

let abs x = if x < 0. then -x else x

let printExpr2 (offset:string) ((op, coef):expr2) =
    let ret = new StringBuilder() in
    let first = ref true in
    mapIter (fun v c ->
        if v = "" then () else
        let cc = abs c in
        if cc = 0. then () else
        let format = (if c < 0. then "-" else if not (!first) then "+" else "") + (if cc <> 1. then "{0}" else "") + "{1}" in
        (ret.AppendFormat(format, cc, v)); first := false) coef;
    ret.Append(if op then " <= " else " < ");
    ret.Append(-(coef.[""]));
    Console.WriteLine(offset + ret.ToString())

let printMatrix (offset:string) =
    Array.iter (fun x ->
        Console.Write(offset);
        Array.iter (fun (x:float) -> Console.Write("{0}\t", x.ToString("0.00"))) x;
        Console.WriteLine())
let printVector (offset:string) (x:float []) =
    let elems = x.Select(fun (x:float) -> x.ToString("0.00")).ToArray() in
    Console.WriteLine("{0}( {1} )", offset, String.Join("\t", elems))

// This procedure sums up all terms according to the variable and move to the
// left-side of the expression. It also flips ">" and ">=" operators to "<" and
// "<=". Returns the operator number (1 <, 3 <>, 4 =, 5 <=) and the mapping from
// a variable to its coefficient. The constant has empty string as a key.
let normalizeExpr (op, t1, t2) =
    let coefs = new coef() in
    let addCoef sign (coef, key) =
        coefs.[key] <-
            if coefs.ContainsKey(key) then
                coefs.[key] + sign * coef
            else sign * coef in
    let sign = if op = 2 || op = 6 then -1. else 1. in
    List.iter (addCoef sign) t1;
    List.iter (addCoef (-sign)) t2;
    mapIter (fun k v -> if k <> "" & v = 0. then coefs.Remove(k); ()) coefs;
    (if sign = -1. then op - 1 else op), coefs

// Copies the given mapping with sign of every coefficient reversed.
let invert (coefs:coef) =
    let r = new coef(coefs) in
    mapIter (fun k v -> r.[k] <- (-v)) r; r

// This procedure normalizes all formulae by sorting out its coefficients, and
// reduces the kinds of operators into only >= and >. It returns the tree
// data structure formed by formula2. The equality is stored as the first value
// of One construct, which appears as the leaf of the tree.
let normalizeOperator formulae =
    let rec Internal opAnd formulae ret =
        match formulae with
        | [] -> ret
        | x :: l ->
            let elem = match x with
                | Expr x ->
                    let (op, coefs) = normalizeExpr x in
                    let pair eq = [One (eq, coefs); One (eq, invert coefs)] in
                    match op with
                    | 1 -> [One (false, coefs)]
                    | 3 -> let l = pair false in if opAnd then [Many l] else l
                    | 4 -> let l = pair true in if opAnd then l else [Many l]
                    | 5 -> [One (true, coefs)]
                | And x -> [Many (Internal true x [])]
                | Or x -> [Many (Internal false x [])] in
            Internal opAnd l (elem @ ret) in
    match formulae with
    | Expr _ -> Internal false [ formulae ] []
    | And x -> [ Many (Internal true x []) ]
    | Or x -> Internal false x []

(* Gaussian elimination routine *)
let eliminate matrix =
    if Array.length !matrix = 0 then () else
    let colLen = Array.length (Array.get !matrix 0) in
    let rec eliminate matrix row col =
        // When the pivoting ends to the last column, end elimination.
        if col = colLen then () else

        // Choose the pivot row, which has the largest absolute value in
        // the current eliminating column.
        let (_, (i, t)) = Array.fold (fun (i, (j, y)) v -> (i + 1,
            if i < row then (-1, 0.) else (* Do not reuse pivot row *)
            let z = Array.get v col in (
            if j = -1 || abs y < abs z then
            (i, z) else (j, y)))) (0, (-1, 0.)) !matrix in

        // If no row has non-zero value in the column, it is skipped.
        let row = if i = -1 then row else (

            // If the pivot row is not at diagonal position, switch.
            let pivot = Array.get !matrix i in
            (if i <> row then
                Array.set !matrix i (Array.get !matrix row);
                Array.set !matrix row pivot);

            // Eliminate other rows' elements by using the pivot row.
            (matrix := Array.mapi (fun j v ->
                if row = j then
                    Array.map (fun x -> x / t) v
                else
                    let s = (Array.get v col) / t in
                    Array.map2 (fun u v -> u - v * s) v pivot) !matrix);
            row + 1) in

        // Recursively process all columns.
        eliminate matrix row (col + 1) in
    eliminate matrix 0 0

let getNoyau matrix =
    let rowLen = Array.length matrix in
    if rowLen = 0 then [] else
    let getRow = Array.get matrix in
    let get row = Array.get (getRow row) in

    let colLen = Array.length (getRow 0) in
    let rec Internal matrix row col pivots ret =
        if col = colLen then ret else

        if row < rowLen & (get row col) = 1. then
            Internal matrix (row + 1) (col + 1) (pivots @ [col]) ret
        else (
            let v = Array.create colLen 0. in
            Array.set v col 1.;
            List.iteri (fun i x -> Array.set v x (-(get i col))) pivots;
            Internal matrix row (col + 1) pivots (ret @ [v])) in
    Internal matrix 0 0 [] []

let getInterpolant (a:expr2 list, b:expr2 list) =
    (* DEBUG: Debug output *)
    Console.WriteLine("Expressions:");
    List.iter (printExpr2 "\t") a;
    Console.WriteLine("    --------------------");
    List.iter (printExpr2 "\t") b;
    Console.WriteLine();

    let ab = List.toArray (a @ b) in
    let abLen = Array.length ab in

    (* Assign indices for all variables *)
    let vars = ref (-1) in
    let varIDs = new Dictionary<string, int>() in
    Array.iter (fun (_, coefs) ->
        mapIter (fun k _ ->
            if not (varIDs.ContainsKey(k) || k = "") then
                (incr vars; varIDs.Add(k, !vars))) coefs) ab;
    let vars = incr vars; !vars in

    (* Create a transposed coefficient matrix *)
    let coefMat = Array.init vars (fun _ -> Array.create abLen 0.) in
    let set var =
        if var <> "" then Array.set (Array.get coefMat varIDs.[var])
        else fun _ _ -> () in
    Array.iteri (fun i (_, coef) -> mapIter (fun k v -> set k i v) coef) ab;

    (* DEBUG: Debug output *)
    Console.WriteLine("Coefficient matrix:");
    printMatrix "\t" coefMat;
    Console.WriteLine();

    (* DEBUG: Debug output *)
    Console.WriteLine("Constants:");
    Array.iter (fun (_, coef:coef) -> Console.Write("\t{0}", -coef.[""])) ab;
    Console.WriteLine();
    Console.WriteLine();

    (* TODO: Support mixed constraints of <= and < *)

    (* Build linear programming problem for OCaml Glpk *)
    (* TODO: Use of SMT solvers as an alternative method *)
    let zcoefs = Array.map (fun _ -> 0.) ab in
    let constrs = Array.create (vars + 2) (Array.create abLen 0.) in
    Array.iteri (fun i a -> Array.set constrs i a) coefMat;
    Array.set constrs vars (Array.create abLen 1.);
    Array.set constrs (vars + 1) (Array.map (fun (_, coef:coef) -> -coef.[""]) ab);
    let pbounds = Array.create (vars + 2) (0., 0.) in
    Array.set pbounds vars (1., infinity);
    Array.set pbounds (vars + 1) (Double.NegativeInfinity, Double.Epsilon);
    let xbounds = Array.create abLen (0., infinity) in
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
    let m = (List.fold (fun f1 (f2, coefs) ->
        let w = prim.[!i] in incr i;
        if w <> 0. then
            mapIter (fun x v ->
                let v = (if m.ContainsKey(x) then m.[x] else 0.) + v * w in
                m.[x] <- v) coefs;
        f1 & f2) true a), m in

    (* DEBUG: Debug output *)
    Console.WriteLine("\n\nInterpolant:");
    printExpr2 "\t" m;

    Console.WriteLine("\n==========");
    ()

let directProduct input =
    let ret = ref [] in
    let rec inner current = function
        | [] -> ret := current :: !ret
        | x :: rest -> List.iter (fun x -> inner (current @ [x]) rest) x in
    inner [] input; !ret

let rec convertNormalForm group : nf =
    List.rev (List.fold (fun l -> function
        | Many x -> (directProduct (convertNormalForm x)) @ l
        | One x -> [x] :: l) [] group)

let test = "x + y >= 2 & y - 2z <= 0 & 3x - z >= 5 ; 2x - y + 3z <= 0"

let formulae = inputUnit Lexer.token (Lexing.LexBuffer<char>.FromString(test))
(* TODO: Check consistency among formulae with = and <> before normalization *)
let proc x = convertNormalForm (normalizeOperator x)
let groups = directProduct (List.map proc formulae)
let a = List.iter (fun (x:nf) -> getInterpolant (x.Item 0, x.Item 1)) groups
