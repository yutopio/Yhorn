open Util
open Types
open Main

let main _ =
  Parser.inputUnit Lexer.token (Lexing.from_channel stdin) |>
  (fun x -> print_endline (printQuery x); x) |>
  solve |>
  getSolution |>

  M.iter (fun k (params, x) ->
    print_endline (k ^ "(" ^ (String.concat "," params) ^ ") : "
                   ^ (printFormula printExpr x)))

let _ = main ()
