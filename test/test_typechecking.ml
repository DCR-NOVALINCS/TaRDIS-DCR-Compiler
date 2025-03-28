(* open OUnit2
open Tardis
open Utils.Result

(** Helper functions *)

let typecheck_from_prog_state prog_state = 
  let prog = prog_state in
  (* Typechecking.typecheck prog *)
  Typing.check_program prog

let error_msg result =
  match result with
  | Ok _ -> ""
  | Error result_log ->
    List.fold_left (fun acc (loc, msg) -> acc ^ Syntax.string_of_loc loc ^ ": " ^ msg ^ "\n") "" result_log 

(** Tests *)

let test_case prog_state exp_ty err_msg = 
  let ty = typecheck_from_prog_state prog_state in
  assert_equal ty exp_ty 
  ~msg:(String.concat "\n" [err_msg; "Output:"; error_msg ty]) 
  ~cmp:(fun x y -> 
          match x, y with
          | Ok _, Ok _ -> true
          | Error _, Error _ -> true
          | _ -> false)
  
  
(* Test suite *)
let test_suite = 
  let open Common in

  (* Default Result Values *)
  let ok = Ok Typing.empty_typecheck_context
  and error = Error [] in

  (* Suite Typechecking *)
  "test suite for typechecking" >::: [

  "primitive types" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/0.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");

  "types between events" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/1.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");

  "type between events and from basic operators" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/2.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");

  "getting types from different events" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/3.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");

  "simple spawn events" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/4.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");

  "double spawn events" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/5.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");

  "redefining types of event labels" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/6.tardisdcr" test_ctxt in
    test_case state ( error ) "Expected error");

  "getting value from a trigger" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/7.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");

  "event label as parameter of a input event" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/8.tardisdcr" test_ctxt in
    test_case state ( error ) "Expected error");

  "mix of event labels as parameter and usage" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/9.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");
    
  "redeclare event label" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/10.tardisdcr" test_ctxt in
    test_case state ( error ) "Expected error");

  "redeclare event label with different type" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/11.tardisdcr" test_ctxt in
    test_case state ( error ) "Expected error");

  "redeclare event label with different type" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/12.tardisdcr" test_ctxt in
    test_case state ( error ) "Expected error");

  "getting event labels from elsewhere" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/13.tardisdcr" test_ctxt in
    test_case state ( error ) "Expected error");

  "getting event label that is not defined" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/14.tardisdcr" test_ctxt in
    test_case state ( error ) "Expected error");

  "getting event label that is not defined with extra properties" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/15.tardisdcr" test_ctxt in
    test_case state ( error ) "Expected error");
    
  "getting trigger values from different spawn scopes" >::
  (fun test_ctxt -> 
    let state = build_state "typechecking/16.tardisdcr" test_ctxt in
    test_case state ( ok ) "Expected ok");
]

let _ = run_test_tt_main test_suite *)