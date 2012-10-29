open Buffer
open Unix
open Util
open Types

let buildScript constrs =
    let vars = ref [] in

    (* Build up code snippets *)
    let b = create 1 in
    let rec inner hierarchy e =
        match e with
        | Expr x -> printExpr ~vars:(Some vars) x
        | And x | Or x ->
            (* DEBUG: rev is for ease of script inspection *)
            let name = "e" ^ (join "_" (List.rev hierarchy)) in

            (* DEBUG: `hierarchy @ [i]` can simply be `i :: hierarchy` *)
            add_string b (name ^ "=[" ^ (join "," (
                mapi (fun i -> inner (hierarchy @ [string_of_int i])) x)) ^ "]\n");
            (match e with And _ -> "And" | Or _ -> "Or") ^ "(" ^ name ^ ")" in
    let root = inner [] constrs in

    (* Variable declaration first *)
    (if (List.length !vars) = 0 then "" else
        (join "," !vars) ^ " = Ints('" ^ (join " " !vars) ^ "')\n") ^

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
