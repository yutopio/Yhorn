open Types
open Util

let main _ =
  Flags.enable_gv := true;
  Flags.debug_z3_lp := true;

  let input =
    match Array.length (Sys.argv) with
      | 1 -> stdin
      | 2 -> let filename = Sys.argv.(1) in open_in (filename)
      | _ -> assert false in

  let clauses =
    Parser.inputUnit Lexer.token (Lexing.from_channel input) in

  print_endline (String.concat "\n" (List.map printHorn clauses));
  print_newline ();

  Horn.solve clauses

let _ = main ()
