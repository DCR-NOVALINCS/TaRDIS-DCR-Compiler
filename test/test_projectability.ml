open OUnit2

(* not correct to depend on preprocessing an typing,... but generating these 
intermediate outputs for each test would require a lot of work - too much 
work... just add previous tests for these modules and take them as part of
the TCB here. *)
let generate_res choreo =
  let open Utils.Results in
  Verification.Preprocessing.preprocess_program choreo
  >>= fun preprocessing_res ->
  Verification.Typing.check_program preprocessing_res >>= fun typecheck_res ->
  Endpoint_projection.Projectability.check choreo typecheck_res

(* Err test-case - expect an Error *)
let err_test_case ~choreo ~err_msg =
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
  >::: [ ( "test 01 when top-level events only, direct data-dep OK."
         >:: fun test_ctxt ->
           let choreo =
             build_state "resources/projectability/data_deps_01_OK" test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "test 02 with top-level events only, direct data-dep OK."
         >:: fun test_ctxt ->
           let choreo =
             build_state "resources/projectability/data_deps_02_OK" test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "test 03 with top-level events only, direct data-dep not visibile."
         >:: fun test_ctxt ->
           let choreo =
             build_state "resources/projectability/data_deps_03_FAIL" test_ctxt
           and err_msg =
             "Test should have failed: not all initiators of e1 are ensured to \
              see e0 (data-dependency issue)"
           in
           err_test_case ~choreo ~err_msg )
       ; ( "test 04 with top-level events only, ambiguous direct data-dep."
         >:: fun test_ctxt ->
           let choreo =
             build_state "resources/projectability/data_deps_04_FAIL" test_ctxt
           and err_msg =
             "Test should have failed: some initiators of e1 observe e0 as a \
              dual event, making the data-dependency reference ambiguous"
           in
           err_test_case ~choreo ~err_msg )
       ; ( "test 05 with top-level events only, direct data-dep ok."
         >:: fun test_ctxt ->
           let choreo =
             build_state "resources/projectability/data_deps_05_OK" test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "test 06 with spawns, ambiguous data-dep." >:: fun test_ctxt ->
           let choreo =
             build_state "resources/projectability/data_deps_06_FAIL" test_ctxt
           and err_msg =
             "Test should have failed: receiver may be CO, and therefore seing \n\
             \            e0 as a dual event (ambiguous dependency"
           in
           err_test_case ~choreo ~err_msg )
       ; ( "visibility - test 01 - exceeds scope" >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_01_FAIL"
               test_ctxt
           and err_msg =
             "Test should have failed: only one CO is ensured to be in-scope \
              with each e1: initiator-set exceeds scope"
           in
           err_test_case ~choreo ~err_msg )
       ; ( "visibility - test 02 - too-narrow scope" >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_02_FAIL"
               test_ctxt
           and err_msg =
             "Test should have failed: only one CO is ensured to be in scope \
              with each e1 but there is no guarantee that it is always \
              CO(cid=3) - must use binding"
           in
           err_test_case ~choreo ~err_msg )
       ; ( "visibility - test 03 - too-narrow scope" >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_03_FAIL"
               test_ctxt
           and err_msg =
             "Test should have failed: only one CO is ensured to be in scope \
              with each e1 but cannot statically guarantee that it coincides \
              with the one being passed via  @trigger - use binding instead"
           in
           err_test_case ~choreo ~err_msg )
       ; ( "visibility - test 04 - too-broad scope" >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_04_FAIL"
               test_ctxt
           and err_msg =
             "Test should have failed: only P's with cid=X are guaranteed to \
              have observed e0 in e1 - unable to statically guarantee \
              X=@trigger.value - use binding instead"
           in
           err_test_case ~choreo ~err_msg )
       ; ( "visibility - test 05 - OK." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_05_OK"
               test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "visibility - test 06 - OK." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_06_OK"
               test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "visibility - test 07 - OK." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_07_OK"
               test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "visibility - test 08 - OK." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_08_OK"
               test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "visibility - test 09 - OK." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_09_OK"
               test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "visibility - test 10 - OK." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_10_OK"
               test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "visibility - test 11 - OK." >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_11_OK"
               test_ctxt
           in
           ok_test_case ~choreo )
       ; ( "visibility - test 12 - out-of-scope" >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_12_FAIL"
               test_ctxt
           and err_msg =
             "Test should have failed: only P(id=4, cid=X) observes e0 and, \
              therefore, the initiator of e1 cannot be in scope."
           in
           err_test_case ~choreo ~err_msg )
       ; ( "visibility - test 13 - out-of-scope" >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_13_FAIL"
               test_ctxt
           and err_msg =
             "Test should have failed: only P s with cid=X are guaranteed to \
              have observed e0 in e1 - receivers of e1 falling out of scope."
           in
           err_test_case ~choreo ~err_msg )
       ; ( "visibility - test 14 - out-of-scope" >:: fun test_ctxt ->
           let choreo =
             build_state
               "resources/projectability/scope_visibility_14_FAIL"
               test_ctxt
           and err_msg =
             "Test should have failed: only the CO with cid=X is guaranteed to \
              have observed e0 in e1 - receivers of e1 falling out of scope."
           in
           err_test_case ~choreo ~err_msg )
           ; ( "visibility - test 15 - OK." >:: fun test_ctxt ->
            let choreo =
              build_state
                "resources/projectability/scope_visibility_15_OK"
                test_ctxt
            in
            ok_test_case ~choreo )
       ]

let _ = run_test_tt_main test_suite
