open Buffer
open Unix
open Util
open Types

let printExprZ3 (op, coef) vars =
    (* TODO: Merge this function with printExpr in main.ml *)
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
    contents b

let buildScript constrs =
    let vars = ref [] in

    (* Build up code snippets *)
    let b = create 1 in
    let rec inner hierarchy e =
        match e with
        | Expr x -> printExprZ3 x vars
        | And x | Or x ->
            (* DEBUG: rev is for ease of script inspection *)
            let name = "e" ^ (join "_" (List.rev hierarchy)) in

            (* DEBUG: `hierarchy @ [i]` can simply be `i :: hierarchy` *)
            add_string b (name ^ "=[" ^ (join "," (
                mapi (fun i -> inner (hierarchy @ [string_of_int i])) x)) ^ "]\n");
            (match e with And _ -> "And" | Or _ -> "Or") ^ "(" ^ name ^ ")" in
    let root = inner [] constrs in

    (* Variable declaration first *)
    (join "," !vars) ^ " = Ints('" ^ (join " " !vars) ^ "')\n" ^

    (* Then buffer contents *)
    (contents b) ^

    (* Finally solve invocation *)
    "solve(" ^ root ^ ")"

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
