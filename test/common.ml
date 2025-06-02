open OUnit2

(** Read-in (parse) test program *)
let set_up (path: string) _test_ctxt = 
  Io.parse_file path

(** Teardown (empty) *)
let teardown _state _test_ctxt = ()

(** Build state for test based on the  *)
let build_state (path_to_test_file: string) test_ctxt = 
  try 
  (bracket (set_up path_to_test_file) teardown test_ctxt);
with Sys_error s ->
  print_endline ("!! Error parsing file: " ^ s);
  exit 1
