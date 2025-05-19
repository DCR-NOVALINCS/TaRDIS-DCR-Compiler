open Frontend

(* let curr_dir = "../../../test/files/" *)

(** Parse from a file path as input *)
let parse_file (path:string) = 
  flush_all ();
  try
    let ic = open_in path in
    let open Lexing in
    let lexbuf = from_channel ic in
    let prog = Parser.main Lexer.read_token lexbuf in
    close_in ic;
    prog
  with Sys_error s -> 
    print_endline ("!! Error parsing file: " ^ s);
    print_endline ("Current directory: " ^ Sys.getcwd ());
    exit 1

(** Parse from a string as input *)
let parse_string (s:string) = 
  let open Lexing in
  let lexbuf = from_string s in
  Parser.main Lexer.read_token lexbuf

(** Parse from a channel as input *)
let parse_channel (ic:in_channel) = 
  let open Lexing in
  let lexbuf = from_channel ic in
  let prog = Parser.main Lexer.read_token lexbuf in
  close_in ic;
  prog

