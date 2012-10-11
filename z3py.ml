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
        (M.iter (fun k v ->
            if v = 0 then () else (
            if not (List.mem k !vars) then vars := k :: !vars;
            if v > 0 && (not !first) then add_char b '+';
            first := false;
            add_string b (string_of_int v);
            add_string b "*";
            add_string b k)) coef;
        if !first then add_string b "0");

        (* Add constraints about p *)
        add_string b (string_of_operator op);
        add_string b "0";
        contents b) constrs in

    (* Suppress trivial solution *)
    let constrs = constrs @ (List.map (fun group ->
        let b = create 1 in
        add_string b "Or(";
        add_string b (join "," (List.map (fun x -> x ^ "!=0") group));
        add_string b ")";
        contents b) nonZero) in

    (* Build Z3Py script *)
    "from z3 import *\n" ^
    (join "," !vars) ^ " = Ints('" ^
    (join " " !vars) ^ "')\n" ^
    "solve(" ^ (join "," constrs) ^ ")\n"

let execute script =
    let (i, o) = open_process "python" in
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
