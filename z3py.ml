open Buffer
open Unix
open Util
open Types

let buildScript (constrs, nonZero) =
    let vars = ref [] in
    let constrs = List.map (fun (op, coef) ->
        (* Build the expression *)
        let b = create 1 in
        let first = ref true in
        M.iter (fun v c ->
            if c = 0 then () else (
            if not (List.mem v !vars) then vars := v :: !vars;
            if c > 0 && not !first then add_char b '+' else if c = -1 then add_char b '-';
            first := false;
            if (abs c) <> 1 then add_string b ((string_of_int c) ^ "*");
            add_string b v)) coef;
        if !first then add_string b "0";
        add_string b (string_of_operator op);
        add_string b "0";
        contents b) constrs in

    (* Suppress trivial solution *)
    let (_, zeroConstrs, orNames) = List.fold_left (fun (i, c, o) group ->
        let name = "o" ^ (string_of_int i) in
        i + 1,
        (name ^ "=[" ^ (join "," (List.map (fun x -> x ^ "!=0") group)) ^ "]") :: c,
        ("Or(" ^ name ^ ")") :: o) (0, [], []) nonZero in

    (* Build Z3Py script *)
    (List.fold_left (fun x v ->
        x ^
        (join "," v) ^ " = Ints('" ^
        (join " " v) ^ "')\n") "" (splitByN 200 !vars)) ^
    (join "\n" zeroConstrs) ^ "\n" ^
    "p=[" ^ (join "," (constrs @ orNames)) ^ "]\n" ^
    "solve(p)"

let execute script =
    let (i, o) = open_process "python" in
    let script = "from z3 import *\n" ^ script in
    output_string o script;
    flush o;
    close_out o;

    let ret = Buffer.create 1 in
    (try
        while true do
            let line = input_line i in
            Buffer.add_string ret line
        done
    with End_of_file -> ());

    let _ = close_process (i, o) in
    Buffer.contents ret

let integer_programming space =
    let script = buildScript space in
    let ret = execute script in
    Z3pyparser.inputUnit Z3pylexer.token (Lexing.from_string ret)
