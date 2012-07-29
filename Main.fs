module Main

open System
open System.Collections.Generic
open Parser

let test = "x + y > 2 & y - 2z < 0 & 3x - z >= 5 ; 2x - y + 3z <= 0"
let data = inputUnit Lexer.token (Lexing.LexBuffer<char>.FromString(test))
