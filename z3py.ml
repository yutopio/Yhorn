open Buffer
open Unix

let buildScript constrs pbounds xbounds =
    let xLen = Array.length xbounds in
    let b1 = create (xLen * 4) in
    let b2 = create (xLen * 4) in
    let c = create 1 in (* Buffer size cannot be estimated *)
    Array.iteri (fun i (low, up) ->
        (* Declare variables *)
        let name = string_of_int i in
        add_string b2 name;
        let name = "x" ^ name in
        add_string b1 name;
        if i + 1 <> xLen then (add_char b1 ','; add_char b2 ' ');

        (* Add constraints about x *)
        if low = up then
            add_string c (name ^ "==" ^ (string_of_int low) ^ ",")
        else (
            if low <> min_int then
                add_string c (name ^ ">=" ^ (string_of_int low) ^ ",");
            if up <> max_int then
                add_string c (name ^ "<=" ^ (string_of_int up) ^ ","))) xbounds;

    Array.iteri (fun i (low, up) ->
        (* Build the expression *)
        let b = create 1 in
        let first = ref true in
        Array.iteri (fun i c ->
            if c = 0 then () else (
            if c > 0 && (not !first) then add_char b '+';
            first := false;
            add_string b (string_of_int c);
            add_string b "*x";
            add_string b (string_of_int i))) constrs.(i);
        if !first then add_string b "0";

        (* Add constraints about p *)
        if low = up then (
            add_buffer c b;
            add_string c ("==" ^ (string_of_int low) ^ ",")
        ) else (
            if low <> min_int then (
                add_buffer c b;
                add_string c (">=" ^ (string_of_int low) ^ ","));
            if up <> max_int then (
                add_buffer c b;
                add_string c ("<=" ^ (string_of_int up) ^ ",")))) pbounds;

    (* Sentinel *)
    add_string c "True";

    (* Build Z3Py script *)
    "from z3 import *\n\n" ^
    (contents b1) ^ " = Ints('" ^ (contents b2) ^ "')\n\n" ^
    "solve(" ^ (contents c) ^ ")\n"

let execute script =
    let (i, o) = open_process "python" in
    output_string o script;
    flush o;
    close_out o;
    let ret = input_line i in
    let _ = close_process (i, o) in
    ret

let integer_programming constrs pbounds xbounds =
    let script = buildScript constrs pbounds xbounds in
    let ret = execute script in
    let assignments = Z3pyparser.inputUnit Z3pylexer.token (Lexing.from_string ret) in
    Array.init (Array.length xbounds) (fun i -> Types.MI.find i assignments)
