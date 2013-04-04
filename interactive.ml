open Util
open Types

let main _ =
  let input =
    match Array.length (Sys.argv) with
      | 1 -> stdin
      | 2 -> let filename = Sys.argv.(1) in open_in (filename)
      | _ -> assert false in

  let clauses, merges =
    Parser.inputUnit Lexer.token (Lexing.from_channel input) in

  print_endline (
    String.concat "\n" (List.map printHorn clauses) ^ "\n" ^
      "[" ^ String.concat "," (List.map (
        fun (a, b) -> Id.print a ^ "-" ^ Id.print b) merges) ^ "]");

  Horn.solve clauses merges |>
  printHornSol |> print_endline

let _ = main ()
