open Types
open Parser
open Lexer
open Main

let main _ =
  let input = inputUnit token (Lexing.from_channel stdin) in
  let solSp = solve input in
  let predAssignments = getSolution solSp in

  print_newline ();
  M.iter (fun k (params, x) ->
    print_endline (k ^ "(" ^ (String.concat "," params) ^ ") : "
                   ^ (printFormula printExpr x))) predAssignments

let _ = main ()
