(* open OUnit2
open Common
open Tardis
open Babel *)

(* let translate_from_prog_state prog_state =
  let prog = from_prog_state prog_state in
  Translate.translate prog

(** Tests *)

let test_case prog_state expected_value err_msg = 
  let value = translate_from_prog_state (prog_state) in
  assert_equal value expected_value 
  ~msg: err_msg 
  ~cmp: (fun x y -> x = y)


let test_suite = "test suite for babel translator/unparser" >::: [
  
]

let _ = run_test_tt_main test_suite *)