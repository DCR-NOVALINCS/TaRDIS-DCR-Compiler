module StringMap = Map.Make (String)

(* let replace str target replacement = let open Str in global_replace
   (regexp_string target) replacement str *)

let unparse_to_file file' res =
  let file = file' in
  let oc = open_out file in
  Printf.fprintf oc "%s\n" res;
  close_out oc

(* let unparse_to_file_with_blob_tmpl dest_file blob_tmpl_str tmpl_context = let
   oc = open_out dest_file in List.iter (fun (k, v) -> Printf.fprintf oc "%s\n"
   @@ replace blob_tmpl_str (Printf.sprintf "// {{%s}}" k) v) tmpl_context;
   close_out oc *)

let print_errors errors =
  let open Frontend.Syntax in
  print_endline "\n== COMPILATION FAILED ==\n  Terminated with errors: ";
  List.iter
    (fun (loc, msg) ->
      print_endline @@ Printf.sprintf "%s: %s\n" (string_of_loc loc) msg)
    errors

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
  |> unparse_to_file "output_tardis.tardisdcr";
  Projectability.check program typecheck_res >>= fun () ->
  (* TODO [post-demo] have projections return something more friendly than the
     entire projection context - need to check what's needed first 
     >> [already] in the making... *)
  Projections.project program ifc_constraints_by_uid |> fun endpoints ->
  let endpoint_encodings = List.map Babel.encode_endpoint_process endpoints in
  List.iter print_endline endpoint_encodings;
  (* Translation.Babel.test_computation_event (); *)
  Ok ()

(* TODO -> List.iter unparsed_projections unparse_projection_to_file *)
(* unparse_to_file_with_blob_tmpl "output_babel.java" ([%blob
   "resources/input_babel.java"]) [ ("code", babel_unparsed) ]; *)
(* print_endline "Compilation succeeded."; flush stdout; exit 0 *)

let main () =
  let lexbuf = Lexing.from_channel stdin in
  match process_choreography lexbuf with
  | Ok () ->
    print_endline "Compilation succeeded.";
    flush stdout;
    exit 0
  | Error err ->
    print_errors err;
    exit 1
(* Terminal input*)

let () = main ()

(* Typing.check_program prog >>= fun _typecheck_res -> *)
(* Projections.project (prog.events, prog.relations) >>= fun projections ->
   Babel.Translate.translate projections >>= fun babel_ctxt -> let unparsed_prog
   = Unparser.unparse_prog ~indent:"" ~abbreviated:false prog in let
   babel_unparsed = Babel.Unparser.unparse ~indent:"\t\t" babel_ctxt in *)
