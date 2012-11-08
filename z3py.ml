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
            let name = "e" ^ (String.concat "_" (List.rev hierarchy)) in

            (* DEBUG: `hierarchy @ [i]` can simply be `i :: hierarchy` *)
            add_string b (name ^ "=[" ^ (String.concat "," (
                mapi (fun i -> inner (hierarchy @ [string_of_int i])) x)) ^ "]\n");
            (match e with And _ -> "And" | Or _ -> "Or") ^ "(" ^ name ^ ")" in
    let root = inner [] constrs in

    (* Variable declaration first *)
    (if (List.length !vars) = 0 then "" else
        (String.concat "," !vars) ^ " = Ints('" ^ (String.concat " " !vars) ^ "')\n") ^

    (* Then buffer contents *)
    (contents b) ^

    (* Finally solve invocation *)
    "solve(" ^ root ^ ")\n"

let (i, o, _) as p = open_process_full "python -i" (environment ())
let lexbuf =
    output_string o "from z3 import *\n";
    flush o;
    Lexing.from_channel i
    (* DEBUG: Uncomment following lines to dump Z3 output.
    Lexing.from_function (fun buf len ->
        let ret = input i buf 0 len in
        print_string (String.sub buf 0 ret);
        ret) *)
let close () = close_process_full p

let integer_programming space =
    let script = buildScript space in
    output_string o script;
    (* DEBUG: Uncomment following line to dump Z3Py script.
    print_endline script; *)
    output_string o "print \"$\"\n";
    flush o;

    Z3pyparser.inputUnit Z3pylexer.token lexbuf
