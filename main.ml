open Glpk
open Parser
open Types
open Z3py

let fabs x = if x < 0. then -.x else x

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

(* Copies the given mapping with sign of every coefficient reversed. *)
let invert = M.map (fun v -> -.v)

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
            if j = -1 || fabs y < fabs z then
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
    let coefMat = Array.make_matrix vars abLen 0 in
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
        print_int (-(M.find "" coef))) ab;
    print_endline "\n\n";

    (* TODO: Support mixed constraints of <= and < *)

    (* Build linear programming problem for OCaml Glpk *)
    (* TODO: Use of SMT solvers as an alternative method *)
    let constrs = Array.make_matrix (vars + 2) abLen 0 in
    Array.iteri (fun i a -> Array.set constrs i a) coefMat;
    Array.set constrs vars (Array.create abLen 1);
    Array.set constrs (vars + 1) (Array.map (fun (_, coef) -> - (M.find "" coef)) ab);
    let pbounds = Array.create (vars + 2) (0, 0) in
    Array.set pbounds vars (1, max_int);
    Array.set pbounds (vars + 1) (min_int, -1);
    let xbounds = Array.create abLen (0, max_int) in
    let prim = integer_programming constrs pbounds xbounds in

    (* DEBUG: Debug output *)
    print_endline "\nLP solution:";
    printVector "\t" prim;

    (* Calculate one interpolant *)
    let i = ref 0 in
    let m = List.fold_left (fun (f1, m) (f2, coefs) ->
        LTE (* FIXME: should evaluate operators of each expression *),
        let w = prim.(!i) in incr i;
        if w = 0 then m else
        M.fold (fun x v m ->
            let v = (if M.mem x m then M.find x m else 0) + v * w in
            M.add x v m) coefs m) (EQ, M.empty) a in

    (* DEBUG: Debug output *)
    print_endline "\n\nInterpolant:";
    printExpr2 "\t" m;

    print_endline "\n=========="

let directProduct input =
    let ret = ref [] in
    let rec inner current = function
        | [] -> ret := current :: !ret
        | x :: rest -> List.iter (fun x -> inner (current @ [x]) rest) x in
    inner [] input; !ret

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

(* FIXME: Buggy input *)
let test = "x = z & y = z ; x >= w & y + 1 <= w"

let formulae = inputUnit Lexer.token (Lexing.from_string test)
let groups = directProduct (List.map convertToDNF formulae)
(* TODO: Check consistency among formulae with = and <> before normalization *)
let a = List.iter (fun x -> getInterpolant (List.hd x) (List.nth x 1)) groups
