open OUnit2
open Common
(** Helper functions *)
open Verification
module TreeMap = Map.Make (String)

let static_ifc_checking_from_prog_state prog_state =
  let open Utils.Results in
  Verification.Preprocessing.preprocess_program prog_state >>= fun preprocessing_res ->
  Verification.Typing.check_program preprocessing_res >>= fun _ ->
  Static_checking.check_static_information_security prog_state


let test_case prog_state exp err_msg =
  let ty = static_ifc_checking_from_prog_state prog_state in
  assert_equal ty exp ~msg:err_msg ~cmp:(fun x y ->
      match (x, y) with
      | Ok _, Ok _ -> true
      | Error _, Error _ -> true
      | _ -> false)

(** Test Suite *)
let test_suite =
  "test suite for static information flow control no params"
  >::: [ 
    ( "Simple test for relation and event data" >:: fun test_ctxt ->
           let state = build_state "resources/static_checking/0.tardisdcr" test_ctxt in
           test_case state (Ok  TreeMap.empty ) "Expected ok" )
       ;
    ( "Testing IFC type expr in input events" >:: fun test_ctxt ->
           let state = build_state "resources/static_checking/0.1.tardisdcr" test_ctxt in
           test_case state (Error []) "Expected Fail" )
        ; 
    ("Testing IFC type expr in input events + relation" >:: fun test_ctxt ->
            let state = build_state "resources/static_checking/0.1.1.tardisdcr" test_ctxt in
                test_case state ( Ok TreeMap.empty ) "Expected Ok in Test 0.1.1") 
     ;
    ( "Testing IFC 0.1.1 but with leak in relations" >::
            (fun test_ctxt ->
              let state = build_state "resources/static_checking/0.1.2.tardisdcr" test_ctxt in
              test_case state ( Error []) "Expected Error in relation") )
      ;
    ( "Testing IFC with multiple security labels" >::
            (fun test_ctxt ->
              let state = build_state "resources/static_checking/0.1.3.tardisdcr" test_ctxt in
              test_case state ( Ok TreeMap.empty ) "Expected Ok in Test 0.1.3") )
      ;
      ( "Testing simple IFC with spawns" >::
            (fun test_ctxt ->
              let state = build_state "resources/static_checking/0.2.tardisdcr" test_ctxt in
              test_case state ( Ok TreeMap.empty ) "Expected Ok in Test 0.2") )
      ;
      ( "Testing simple IFC with spawns" >::
      (fun test_ctxt ->
        let state = build_state "resources/static_checking/0.2.tardisdcr" test_ctxt in
        test_case state ( Ok TreeMap.empty ) "Expected Ok in Test 0.2") )
;

   
  ]

let _ = run_test_tt_main test_suite
