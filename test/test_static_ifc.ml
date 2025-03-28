(* open OUnit2
open Common
open Utils.Result
open Tardis.Static_checking
open Tardis.Syntax
open Tardis.Parser
open Tardis.Lexer

(** Helper functions *)

let static_ifc_checking_from_prog_state prog_state = 
  let prog = prog_state in
  typecheck_static_ifc prog 

  let error_msg result =
    match result with
    | Ok _ -> ""
    | Error result_log ->
      List.fold_left (fun acc (loc, msg) -> acc ^ string_of_loc loc ^ ": " ^ msg ^ "\n") "" result_log 
  
(** Tests *)

let test_case prog_state exp err_msg = 
  let ty = static_ifc_checking_from_prog_state prog_state in
  assert_equal ty exp ~msg:err_msg ~cmp:(fun x y -> 

      match x, y with
      | Ok _, Ok _ -> true
      | Error _, Error _ -> true
      | _ -> false)

(** Test Suite *)
let test_suite = 
  

  "test suite for static information flow control" >::: [
      
    "Simple testing" >:: 
    (fun test_ctxt -> 
      let state = build_state "static_checking/0.tardisdcr" test_ctxt in
      test_case state ( Ok() ) "Expected ok");

    "Testing IFC type expr in input events" >:: 
      (fun test_ctxt -> 
        let state = build_state "static_checking/0.1.tardisdcr" test_ctxt in
        test_case state ( Error [] ) "Expected Fail");
(* 
    "Testing IFC " >:: 
      (fun test_ctxt -> 
        let state = build_state "static_checking/1.tardisdcr" test_ctxt in
        test_case state ( Ok() ) "Expected Ok in Test 1.");
        
    "Testing IFC Spawn" >:: 
    (fun test_ctxt -> 
      let state = build_state "static_checking/1.1.tardisdcr" test_ctxt in
      test_case state ( Ok() ) "Expected Ok in Test 1.1"); *)
]

let _ = run_test_tt_main test_suite *)