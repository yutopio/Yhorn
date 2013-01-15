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
let identStartChar = letter | '_'
let identChar = letter | digit | '_'
let ident = identStartChar identChar*

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
    | '&'               { AND }
    | '|'               { OR }
    | '!'               { NOT }
    | ';'               { SEMICOLON }
    | ident             { IDENT(Id.from_string (lexeme lexbuf)) }
    | digit+            { INT(int_of_string(lexeme lexbuf)) }
    | eof               { EOF }
    | _                 { unrecToken (lexeme lexbuf) }
and blockComment = parse
    | "*/"              { token lexbuf }
    | [^'*''/']+        { blockComment lexbuf }
    | '*'+[^'*''/']     { blockComment lexbuf }
    | eof               { nonTermCom () }
    | _                 { blockComment lexbuf }
