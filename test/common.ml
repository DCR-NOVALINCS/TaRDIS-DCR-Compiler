open OUnit2
open Io
open Utils

(** Parses a file and returns the program *)

(** Setups test context to contain information about the program, the node environment and lattive environment *)
let setup (path: string) _test_ctxt = 
  let path = Io.curr_dir ^ path in
  parse_file path
  (* (parse_file path, Env.empty_env, Env.empty_env) *)

(** Teardown function for the test context *)
let teardown _state _test_ctxt = ()

(** Builds the context of the tests, given a filepath of a reda program*)
let build_state (path: string) test_ctxt = bracket (setup path) teardown test_ctxt
