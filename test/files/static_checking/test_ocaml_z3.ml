open Z3;;

(* Context and solver setup *)
let ctx = Z3.mk_context [] in
let solver = Z3.Solver.mk_solver ctx None in
(* Declare sorts *)
let string_sort = Z3.Seq.mk_string_sort ctx in
let event_sort = Z3.Sort.mk_uninterpreted_s ctx "Event" in

(* Declare constants for 'cc' and 'cc@trigger' of sort Event *)
let cc = Z3.Expr.mk_const_s ctx "cc" event_sort in
let trigger = Z3.Expr.mk_const_s ctx "cc@trigger" event_sort in
let e1 = Z3.Boolean.mk_eq ctx cc trigger in
(* Add first equality to the solver *)
Z3.Solver.add solver [e1];

(* Push the solver state *)
Z3.Solver.push solver;

(* Declare constants for communityInfo and its field 'value.cid' *)
let community_info = Z3.Expr.mk_const_s ctx "communityInfo" event_sort in
let ci_cid = Z3.Expr.mk_const_s ctx "communityInfo.value.cid" event_sort in
let field = Z3.Expr.mk_const_s ctx "cc@trigger.value.cid" event_sort in
let e2 = Z3.Boolean.mk_eq ctx ci_cid field in
(* Add the second equality to the solver *)

(* Use an uninterpreted function to represent the 'value.cid' field *)
(* let cid_func = Z3.FuncDecl.mk_func_decl_s ctx "value.cid" [event_sort] string_sort in
let community_info_cid = Z3.Expr.mk_app ctx cid_func [community_info] in *)

(* Create a string constant 'cc@trigger.value.cid' *)
(* let e2 = Z3.Boolean.mk_eq ctx community_info_cid expected_cid in *)

(* Add the second equality to the solver *)
(* Z3.Solver.add solver [e2];
let cp = Z3.Expr.mk_const_s ctx "cp" event_sort in
let cp_trigger = Z3.Expr.mk_const_s ctx "cp@trigger" event_sort in
let e3 = Z3.Boolean.mk_eq ctx cp cp_trigger in
Z3.Solver.add solver [e3];
(* Push the solver state *)
Z3.Solver.add solver [ (Z3.Boolean.mk_eq ctx cp community_info) ];
Z3.Solver.push solver; *)

(* Declare constants for 'cp' and 'cp@trigger' of sort Event *)

(* let e9 = Z3.Boolean.mk_not ctx (Z3.Boolean.mk_eq ctx cp community_info) in
(* Add the third equality to the solver *)
Z3.Solver.add solver [e9]; *)

(* Compare 'cp@trigger.value.cid' and 'communityInfo.value.cid' using the uninterpreted function *)
(* let cp_trigger_cid = Z3.Expr.mk_app ctx cid_func [cp_trigger] in
let community_info_cid2 = Z3.Expr.mk_app ctx cid_func [community_info] in
let e4 = Z3.Boolean.mk_eq ctx cp_trigger_cid community_info_cid2 in *)
let e8 = Z3.Expr.mk_const_s ctx "cp.value.pid" event_sort in
let cp_trigger = Z3.Expr.mk_const_s ctx "cp@trigger.value.pid" event_sort in
let e7 = Z3.Boolean.mk_eq ctx e8 cp_trigger in
Z3.Solver.add solver [e7];
(* Check satisfiability of the final condition *)
let field_2 = Z3.Expr.mk_const_s ctx "cc@trigger.value.cid" event_sort in
let cp_trigger3 = Z3.Expr.mk_const_s ctx "cp@trigger.value.pid" event_sort in
let e6 = Z3.Boolean.mk_eq ctx field_2 cp_trigger3 in
match Z3.Solver.check solver [e6] with
| Z3.Solver.SATISFIABLE -> 
    Printf.printf "Satisfiable\n";
    Printf.printf "%s\n" (Z3.Model.to_string (Option.get (Z3.Solver.get_model solver)))
| Z3.Solver.UNSATISFIABLE -> Printf.printf "Unsatisfiable\n" ;
let unsat_core = Z3.Solver.get_unsat_core solver in Printf.printf "Unsat core: %s\n" (String.concat ", " (List.map Z3.Expr.to_string unsat_core))
| Z3.Solver.UNKNOWN -> Printf.printf "Unknown\n"
