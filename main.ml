open Glpk
open Parser
open Types

let abs x = if x < 0. then -.x else x

let printExpr2 offset (op, coef) =
    print_string offset;
    let first = ref true in
    M.iter (fun v c ->
        if v = "" || c = 0. then () else (
        print_string (if c < 0. then "-" else if not (!first) then "+" else "");
        let cc = abs c in if cc <> 1. then print_float cc;
        print_string v);
        first := false) coef;
    print_string (if op then " <= " else " < ");
    print_float (-.(M.find "" coef));
    print_newline ()

let printMatrix offset =
    Array.iter (fun x ->
        print_string offset;
        Array.iter (fun x -> print_float x; print_string "\t") x;
        print_newline ())

let printVector offset x =
    print_string (offset ^ "( ");
    let len = Array.length x in
    Array.iteri (fun i x ->
        print_float x;
        print_string (if i = len - 1 then "" else "\t")) x;
    print_endline ")"

(* This procedure sums up all terms according to the variable and move to the
   left-side of the expression. It also flips ">" and ">=" operators to "<" and
   "<=". Returns the operator number (1 <, 3 <>, 4 =, 5 <=) and the mapping from
   a variable to its coefficient. The constant has empty string as a key. *)
let normalizeExpr (op, t1, t2) =
    let addCoef sign coefs (coef, key) =
        M.add key (sign *. coef +.
            (if M.mem key coefs then M.find key coefs else 0.)) coefs in
    let sign = if op = 2 || op = 6 then -1. else 1. in
    let coefs = List.fold_left (addCoef sign) M.empty t1 in
    let coefs = List.fold_left (addCoef (-.sign)) coefs t2 in
    let coefs = M.fold (fun k v coefs ->
        if k <> "" && v = 0. then M.remove k coefs else coefs) coefs coefs in
    (if sign = -1. then op - 1 else op), coefs

(* Copies the given mapping with sign of every coefficient reversed. *)
let invert = M.map (fun v -> -.v)

(* This procedure normalizes all formulae by sorting out its coefficients, and
   reduces the kinds of operators into only >= and >. It returns the tree
   data structure formed by formula2. The equality is stored as the first value
   of One construct, which appears as the leaf of the tree. *)
let normalizeOperator formulae =
    let rec internal opAnd formulae ret =
        match formulae with
        | [] -> ret
        | x :: l ->
            let elem = match x with
                | Expr x ->
                    let (op, coefs) = normalizeExpr x in
                    let pair eq = [One (eq, coefs); One (eq, invert coefs)] in (
                    match op with
                    | 1 -> [One (false, coefs)]
                    | 3 -> let l = pair false in if opAnd then [Many l] else l
                    | 4 -> let l = pair true in if opAnd then l else [Many l]
                    | 5 -> [One (true, coefs)])
                | And x -> [Many (internal true x [])]
                | Or x -> [Many (internal false x [])] in
            internal opAnd l (elem @ ret) in
    match formulae with
    | Expr _ -> internal false [ formulae ] []
    | And x -> [ Many (internal true x []) ]
    | Or x -> internal false x []

(* Gaussian elimination routine *)
let eliminate matrix =
    if Array.length !matrix = 0 then () else
    let colLen = Array.length (Array.get !matrix 0) in
    let rec eliminate matrix row col =
        (* When the pivoting ends to the last column, end elimination. *)
        if col = colLen then () else

        (* Choose the pivot row, which has the largest absolute value in
           the current eliminating column. *)
        let (_, (i, t)) = Array.fold_left (fun (i, (j, y)) v -> (i + 1,
            if i < row then (-1, 0.) else (* Do not reuse pivot row *)
            let z = Array.get v col in (
            if j = -1 || abs y < abs z then
            (i, z) else (j, y)))) (0, (-1, 0.)) !matrix in

        (* If no row has non-zero value in the column, it is skipped. *)
        let row = if i = -1 then row else (

            (* If the pivot row is not at diagonal position, switch. *)
            let pivot = Array.get !matrix i in
            (if i <> row then
                Array.set !matrix i (Array.get !matrix row);
                Array.set !matrix row pivot);

            (* Eliminate other rows' elements by using the pivot row. *)
            (matrix := Array.mapi (fun j v ->
                if row = j then
                    Array.map (fun x -> x /. t) v
                else
                    let s = (Array.get v col) /. t in
                    Array.mapi (fun i u ->
                        let v = Array.get pivot i in
                        u -. v *. s) v) !matrix);
            row + 1) in

        (* Recursively process all columns. *)
        eliminate matrix row (col + 1) in
    eliminate matrix 0 0

let getNoyau matrix =
    let rowLen = Array.length matrix in
    if rowLen = 0 then [] else
    let getRow = Array.get matrix in
    let get row = Array.get (getRow row) in

    let colLen = Array.length (getRow 0) in
    let rec internal matrix row col pivots ret =
        if col = colLen then ret else

        if row < rowLen & (get row col) = 1. then
            internal matrix (row + 1) (col + 1) (pivots @ [col]) ret
        else (
            let v = Array.create colLen 0. in
            Array.set v col 1.;
            let i = ref 0 in
            List.iter (fun x -> Array.set v x (-.(get !i col)); incr i) pivots;
            internal matrix row (col + 1) pivots (ret @ [v])) in
    internal matrix 0 0 [] []

let listToArray l =
    let len = List.length l in
    if len = 0 then [| |] else
    let ret = Array.make len (List.hd l) in
    let i = ref 0 in
    List.iter (fun x -> Array.set ret !i x; incr i) l;
    ret

let arrayFold2 f x a =
    let i = ref (-1) in
    Array.fold_left (fun x -> f x (Array.get a (incr i; !i))) x

let getInterpolant a b =
    (* DEBUG: Debug output *)
    print_endline "Expressions:";
    List.iter (printExpr2 "\t") a;
    print_endline "    --------------------";
    List.iter (printExpr2 "\t") b;
    print_endline "\n";

    let ab = listToArray (a @ b) in
    let abLen = Array.length ab in

    (* Assign indices for all variables *)
    let vars = ref (-1) in
    let varIDs = Array.fold_left (fun m (_, coefs) ->
        M.fold (fun k _ m ->
            if not (M.mem k m || k = "") then
                (incr vars; M.add k !vars m) else m) coefs m) M.empty ab in
    let vars = incr vars; !vars in

    (* Create a transposed coefficient matrix *)
    let coefMat = Array.make_matrix vars abLen 0. in
    let set var =
        if var <> "" then Array.set (Array.get coefMat (M.find var varIDs))
        else fun _ _ -> () in
    Array.iteri (fun i (_, coef) -> M.iter (fun k v -> set k i v) coef) ab;

    (* DEBUG: Debug output *)
    print_endline "Coefficient matrix:";
    printMatrix "\t" coefMat;
    print_endline "\n";

    (* DEBUG: Debug output *)
    print_endline "Constants:";
    Array.iter (fun (_, coef) ->
        print_string "\t";
        print_float (-.(M.find "" coef))) ab;
    print_endline "\n\n";

    (* Build linear programming problem for OCaml Glpk *)
    let zcoefs = Array.map (fun (_, coef) -> -.(M.find "" coef)) ab in
    let constrs = Array.make_matrix (vars + 1) abLen 0. in
    Array.iteri (fun i a -> Array.set constrs i a) coefMat;
    Array.set constrs vars zcoefs;
    let pbounds = Array.create (vars + 1) (0., 0.) in
    Array.set pbounds vars (-100., 0.);
    let xbounds = Array.create abLen (0., infinity) in
    let lp = make_problem Minimize zcoefs constrs pbounds xbounds in
    set_message_level lp 0;
    scale_problem lp;
    use_presolver lp true;
    simplex lp;

    (* DEBUG: Debug output *)
    let prim = get_col_primals lp in
    print_endline "\n\nLP solution:";
    printVector "\t" prim;
    print_endline "\n=========="

let directProduct input =
    let ret = ref [] in
    let rec inner current = function
        | [] -> ret := current :: !ret
        | x :: rest -> List.iter (fun x -> inner (current @ [x]) rest) x in
    inner [] input; !ret

let rec convertNormalForm group : nf =
    List.rev (List.fold_left (fun l -> function
        | Many x -> (directProduct (convertNormalForm x)) @ l
        | One x -> [x] :: l) [] group)

let test = "x + y >= 2 & y - 2z <= 0 & 3x - z >= 5 ; 2x - y + 3z <= 0"
let formulae = inputUnit Lexer.token (Lexing.from_string test)
let proc x = convertNormalForm (normalizeOperator x)
let groups = directProduct (List.map proc formulae)
let a = List.iter (fun x -> getInterpolant (List.hd x) (List.nth x 1)) groups
