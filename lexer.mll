{
open Error
open Lexing
open Parser
open Types
}

let br = ['\r' '\n']
let sp = [' ' '\t']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let letter = lower | upper
let nonEscChars = [^ '"' '\'' '\\' '0' 'n' 'r' 't']
let identChar = letter | digit | '_'
let lowerIdent = (lower | '_') identChar*
let upperIdent = (upper | '_') identChar*

rule token = parse
    | sp+               { token lexbuf }
    | br+               { token lexbuf }
    | "/*"              { blockComment lexbuf }
    | "<="              { OP(LTE) }
    | ">="              { OP(GTE) }
    | "<>"              { OP(NEQ) }
    | "!="              { OP(NEQ) }
    | "=="              { OP(EQ) }
    | '<'               { OP(LT) }
    | '>'               { OP(GT) }
    | '='               { OP(EQ) }
    | '+'               { PLUS }
    | '-'               { MINUS }
    | '('               { LPAREN }
    | ')'               { RPAREN }
    | '['               { LBRACK }
    | ']'               { RBRACK }
    | '&'               { AND }
    | '|'               { OR }
    | '!'               { NOT }
    | '.'               { DOT }
    | "->"              { ARROW }
    | ','               { COMMA }
    | lowerIdent        { VAR(Id.from_string (lexeme lexbuf)) }
    | upperIdent        { PRED(Id.from_string (lexeme lexbuf)) }
    | digit+            { INT(int_of_string(lexeme lexbuf)) }
    | eof               { EOF }
    | _                 { failwith (unrecToken (lexeme lexbuf)) }
and blockComment = parse
    | "*/"              { token lexbuf }
    | [^'*''/']+        { blockComment lexbuf }
    | '*'+[^'*''/']     { blockComment lexbuf }
    | eof               { failwith nonTermCom }
    | _                 { blockComment lexbuf }
