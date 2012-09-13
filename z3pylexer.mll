{
open Lexing
open Error
open Z3pyparser
}

let br = ['\r' '\n']
let sp = [' ' '\t']
let digit = ['0'-'9']
let sign = '+' | '-'
let int = sign? digit+

rule token = parse
    | sp+   { token lexbuf }
    | br+   { token lexbuf }
    | '['   { LBR }
    | ']'   { RBR }
    | '='   { EQ }
    | ','   { COMMA }
    | int   { INT(int_of_string(lexeme lexbuf)) }
    | eof   { EOF }
    | _     { z3UnrecOutput (lexeme lexbuf) }
