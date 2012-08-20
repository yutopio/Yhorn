
exception ApplicationException of string

let error msg = raise (ApplicationException msg)

(*** Lexer ***)
let unrecToken token = error ("Unrecognized token: " ^ token)
