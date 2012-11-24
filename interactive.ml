open Yint.Types
open Yint.Parser
open Yint.Lexer
open Yint.Main

let main _ =
  let input = inputUnit token (Lexing.from_channel stdin) in
  let solSp = solve input in
  let predAssignments = getSolution solSp in

  print_newline ();
  M.iter (fun k x ->
    print_endline (k ^ ": " ^ (printFormula printExpr x))) predAssignments

let _ = main ()
