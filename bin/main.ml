module StringMap = Map.Make (String)

let output_dir = "./_out"

let write_to_file filename res =
  let file = Filename.concat output_dir filename in
  let oc = open_out file in
  Printf.fprintf oc "%s\n" res;
  close_out oc

let parse_program lexbuf =
  let open Frontend in
  try Ok (Parser.main Lexer.read_token lexbuf) with
  | Lexer.Lexical_error (loc, msg) -> Error [ (loc, "Lexing error: " ^ msg) ]
  | Frontend.Parser.Error ->
    let loc =
      Frontend.Syntax.Location (lexbuf.lex_start_p, lexbuf.lex_curr_p)
    in
    Error [ (loc, "Syntax error") ]

let parse_verify_program lexbuf =
  let open Verification in
  let open Utils.Results in
  parse_program lexbuf >>= fun program ->
  print_endline @@ Frontend.Unparser.unparse_prog program;
  Preprocessing.preprocess_program program >>= fun preprocessing_res ->
  Typing.check_program preprocessing_res >>= fun typecheck_res ->
  print_endline "Typecheck succeeded.";
  Ok (typecheck_res, program)

let process_choreography lexbuf =
  let open Utils.Results in
  let open Endpoint_projection in
  let open Translation in
  parse_verify_program lexbuf >>= fun (typecheck_res, program) ->
  Verification.Static_checking.check_static_information_security program
  >>= fun ifc_constraints_by_uid ->
  Frontend.Unparser.unparse_prog ~abbreviated:true program
  (* exceptions may occurr here due to IO - currently ignoring these *)
  |> write_to_file "choreo";
  Projectability.check program typecheck_res >>= fun () ->
  Projections.project program ifc_constraints_by_uid |> fun endpoints ->
  let endpoint_encodings = List.map Babel.encode_endpoint_process endpoints in
  Ok endpoint_encodings

let prep_output_dir () =
  (* rmdir -rf  *)
  let rec rmrf path =
    match Sys.is_directory path with
    | true ->
      Sys.readdir path
      |> Array.iter (fun name -> rmrf (Filename.concat path name));
      Sys.rmdir path
    | false -> Sys.remove path
  in
  if Sys.file_exists output_dir then
  rmrf output_dir;
  Sys.mkdir output_dir 0o777

let main () =
  let open Translation in
  prep_output_dir ();
  let lexbuf = Lexing.from_channel stdin in
  match process_choreography lexbuf with
  | Ok endpoints ->
    List.iter
      (fun (role, endpoint) -> write_to_file (role ^ ".json") endpoint)
      endpoints;
    print_endline "Compilation succeeded.";
    flush stdout;
    exit 0
  | Error err ->
    let print_errors errors =
      let open Frontend.Syntax in
      print_endline "Compilation failed with errors: ";
      List.iter
        (fun (loc, msg) ->
          print_endline @@ Printf.sprintf "%s: %s\n" (string_of_loc loc) msg)
        errors
    in
    print_errors err;
    write_to_file "compile_error.json" (Babel.encode_error err);
    exit 1

let () = main ()
