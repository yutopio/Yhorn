{
open Lexing
open Error
open Types
open Parser
}

let br = ['\r' '\n']
let sp = [' ' '\t']
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let nonEscChars = [^ '"' '\'' '\\' '0' 'n' 'r' 't']
let identChar = letter | '_'
let floatp = digit+ '.' digit*
let floate = digit+ ('.' digit* )? ('e'| 'E') ['+' '-']? digit+
let float = digit+ | floatp | floate

rule token = parse
    | sp+               { token lexbuf }
    | br+               { token lexbuf }
    | "<="              { OP(5) }
    | ">="              { OP(6) }
    | "<>"              { OP(3); unrecToken "<>" }
    | '<'               { OP(1); unrecToken "<" }
    | '>'               { OP(2); unrecToken ">" }
    | '='               { OP(4) }
    | '+'               { PLUS }
    | '-'               { MINUS }
    | '('               { LPAREN }
    | ')'               { RPAREN }
    | '&'               { AND }
    | '|'               { OR }
    | ';'               { SEMICOLON }
    | identChar+        { IDENT(lexeme lexbuf) }
    | float             { FLOAT(float_of_string(lexeme lexbuf)) }
    | eof               { EOF }
    | _                 { unrecToken (lexeme lexbuf) }