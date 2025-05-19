open OUnit2

(* not correct to depend on preprocessing an typing,... but generating these 
intermediate outputs for each test would require a lot of work - too much 
work... *)
let generate_res choreo =
  let open Utils.Results in
  Verification.Preprocessing.preprocess_program choreo
  >>= fun preprocessing_res ->
  Verification.Typing.check_program preprocessing_res >>= fun typecheck_res ->
  Endpoint_projection.Projectability.check choreo typecheck_res

(* let error_msg result =
  match result with
  | Ok _ -> ""
  | Error result_log ->
    List.fold_left
      (fun acc (loc, msg) -> acc ^ Syntax.string_of_loc loc ^ ": " ^ msg ^ "\n")
      ""
      result_log *)

(** Tests *)

(* | Error _, Error _ ->
  (* TODO refine this to the expected type of error *)
  true *)

(* Err test-case - expect an Error *)
let err_test_case ~choreo ~err_msg =
  let open Utils.Results in
  let res = generate_res choreo in
  assert_equal res (Error []) ~msg:err_msg ~cmp:(fun x y ->
      match (x, y) with
      | Error _, Error _ -> true
      | _ -> false)

(* Ok test-case - expect an OK _ *)
let ok_test_case ~choreo =
  let msg = "Test should have succeeded." in
  let res = generate_res choreo in
  assert_equal res (Ok ()) ~msg ~cmp:(fun x y ->
      match (x, y) with
      | Ok _, Ok _ -> true
      | _ -> false)

let test_suite =
  let open Common in
  "testing expected projectability-check results"
  >::: [ ( "test 01 when top-level events only, direct data-dep OK." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/01_top_level_data_dep_OK"
               test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "test 02 when top-level events only, direct data-dep not visibile." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/02_top_level_data_dep_FAIL"
               test_ctxt
           and err_msg =
             "Test should have failed: not all initiators of e1 are ensured \
              to see e0 (data-dependency issue)"
           in
           err_test_case ~choreo ~err_msg )
       ]

let _ = run_test_tt_main test_suite
