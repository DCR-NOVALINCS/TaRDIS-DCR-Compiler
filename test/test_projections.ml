(* open OUnit2 *)
(* open Common *)

(** Helper functions *)

(** Tests *)

(* let test_0 prog_state = 
  let _prog = from_prog_state prog_state in
  assert_equal 1 1

(** Test Suite *)
let test_suite = "test suite for projections" >::: [
  "test0" >:: 
  (fun test_ctxt -> 
    let state = build_state "structure.tardisdcr" test_ctxt in
    test_0 state);
]

let _ = run_test_tt_main test_suite *)