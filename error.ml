
exception ApplicationException of string

let error msg = raise (ApplicationException msg)

(*** Lexer ***)
let unrecToken token = error ("Unrecognized token: " ^ token)

(*** Z3PyLexer ***)
let z3UnrecOutput token = error ("Unrecognized output by Z3: " ^ token)
