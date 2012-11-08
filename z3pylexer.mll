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
let letter = ['a'-'z' 'A'-'Z']
let identChar = letter | digit | '_'
let ident = letter identChar*

rule token = parse
    | "no solution" { NO_SOL }
    | sp+   { token lexbuf }
    | br+   { token lexbuf }
    | '['   { LBR }
    | ']'   { RBR }
    | '='   { EQ }
    | ','   { COMMA }
    | int   { INT(int_of_string(lexeme lexbuf)) }
    | ident { STR(lexeme lexbuf) }
    | '$'   { EOI }
    | eof   { EOF (* DEBUG: export OCAMLRUNPARAM=p *) }
    | _     { z3UnrecOutput (lexeme lexbuf) }
