module Main

open System
open System.Collections.Generic
open System.Linq
open Parser
open Types

type coefMap = Dictionary<string, float>

// This procedure sums up all terms according to the variable and move to the
// left-side of the expression. It also flips "<" and "<=" operators to ">" and
// ">=". Returns the operator number (2 >, 3 <>, 4 =, 6 >=) and the mapping from
// a variable to its coefficient. The constant has empty string as a key.
let normalizeExpr (op, t1, t2) =
    let coefs = new Dictionary<string, float>() in
    let addCoef sign (coef, var) =
        let key = match var with Some x -> x | None -> "" in
        coefs.[key] <-
            if coefs.ContainsKey(key) then
                coefs.[key] + sign * coef
            else sign * coef
    List.iter (addCoef (if op % 2 = 0 then 1. else -1.)) t1;
    List.iter (addCoef (if op % 2 = 0 then -1. else 1.)) t2;
    (if op = 1 || op = 5 then op + 1 else op), coefs

// Copies the given mapping with sign of every coefficient reversed.
let invert (coefs:Dictionary<string, float>) =
    let r = new Dictionary<string, float>(coefs) in
    Array.iter (fun k -> r.[k] <- -r.[k]) (coefs.Keys.ToArray()); r

// This procedure normalizes all formulae by sorting out its coefficients, and
// reduces the kinds of operators into only >= and >. It returns the tree
// data structure formed by formula2. The equality is stored as the first value
// of One construct, which appears as the leaf of the tree.
let rec normalizeGroupInternal opAnd formulae ret =
    match formulae with
    | [] -> ret
    | x :: l ->
        let elem = match x with
            | Expr x ->
                let (op, coefs) = normalizeExpr x in
                let pair eq = [One (eq, coefs); One (eq, invert coefs)] in
                match op with
                | 2 -> [One (false, coefs)]
                | 3 -> let l = pair false in if opAnd then [Many l] else l
                | 4 -> let l = pair true in if opAnd then l else [Many l]
                | 6 -> [One (true, coefs)]
            | And x -> [Many (normalizeGroupInternal true x [])]
            | Or x -> [Many (normalizeGroupInternal false x [])] in
        normalizeGroupInternal opAnd l (elem @ ret)
let normalizeOperator formulae =
    match formulae with
    | Expr _ -> normalizeGroupInternal false [ formulae ] []
    | And x -> [ Many (normalizeGroupInternal true x []) ]
    | Or x -> normalizeGroupInternal false x []

let eliminate matrix =
    let rec eliminate matrix col row =
        // When the pivoting ends to the last column, end elimination.
        if col = Array.length (Array.get !matrix 0) then () else

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
            (if i <> row then
                let temp = Array.get !matrix i in
                Array.set !matrix i (Array.get !matrix row);
                Array.set !matrix row temp);

            // Otherwise i-th row is chosen for the pivot.
            let pivot = Array.get !matrix row in
            (matrix := Array.mapi (fun j v ->
                if row = j then
                    Array.map (fun x -> x / t) v
                else
                    let s = -(Array.get v col) / t in
                    Array.map2 (fun u v -> u + v * s) v pivot) !matrix);
            row + 1) in

        // Recursively process all columns.
        eliminate matrix (col + 1) row in
    eliminate matrix 0 0

let processConjunction (coefs:coefMap list) =
    let mapIter f (dic:coefMap) =
        Array.iter (fun k -> f k dic.[k]) (dic.Keys.ToArray()) in

    (* Assign indices for all variables *)
    let keyIDs = new Dictionary<string, int>() in
    List.iter (fun (coefs:coefMap) ->
        let keyID = ref 0 in
        mapIter (fun k _ ->
            if not (keyIDs.ContainsKey(k) || k = "") then
                (keyIDs.Add(k, !keyID); incr keyID)) coefs) coefs;

    (* Create a transposed coefficient matrix *)
    let coefMat = ref (Array.init (keyIDs.Count - 1) (
        fun _ -> Array.create (coefs.Length) 0.)) in
    let set var = Array.set (Array.get !coefMat keyIDs.[var])
    List.iteri (fun i (coefs:coefMap) ->
        mapIter (fun k v -> set k i v) coefs) coefs;

    (* Do Gaussian elimination *)
    let abs x = if x < 0. then -x else x
    eliminate coefMat;

    (* TODO: Get the kernel for the matrix *)
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
        | One(x, y) -> [x,y] :: l) [] group)

let test = "x + y > 2 & y - 2z < 0 & 3x - z >= 5 ; 2x - y + 3z <= 0"
let (g1, g2) = inputUnit Lexer.token (Lexing.LexBuffer<char>.FromString(test))
let proc x = convertNormalForm (normalizeOperator x)
let groups = directProduct (List.map proc [g1 ; g2])
let _ = groups
