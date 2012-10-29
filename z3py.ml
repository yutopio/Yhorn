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
    "solve(" ^ root ^ ")\n"

let (i, o) = open_process "python -i"
let lexbuf =
    output_string o "from z3 import *\n";
    output_string o "import sys\n";
    flush o;
    Lexing.from_channel i
let close () = close_process (i, o)

let integer_programming space =
    let script = buildScript space in
    output_string o script;
    output_string o "print \"\\n$\\n\"\n";
    flush o;

    Z3pyparser.inputUnit Z3pylexer.token lexbuf
