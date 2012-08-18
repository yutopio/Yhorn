module Error

open System

let error msg = raise (new System.ApplicationException(msg))

(*** Lexer ***)
let unrecToken token = error ("Unrecognized token: " + token)
