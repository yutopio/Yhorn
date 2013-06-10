
(*** Lexer ***)
let unrecToken token = "Unrecognized token: " ^ token
let nonTermCom = "End-of-file found, '*/' expected"

(*** Z3 Interface ***)
let z3_error msg = "Z3 error: " ^ msg
let z3_solver_undef msg = "Z3 returned L_UNDEF: " ^ msg
