open Z3;;


(* Context and solver setup *)


let ctx = Z3.mk_context [] in
let solver = Z3.Solver.mk_solver ctx None in

(* Declare sorts *)
let string_sort = Z3.Seq.mk_string_sort ctx in
let cc = Z3.Expr.mk_const ctx (Symbol.mk_string ctx "cc") string_sort in

let t = Z3.Expr.mk_const ctx (Symbol.mk_string ctx "cc@trigger") string_sort in
let e1 = Z3.Boolean.mk_eq ctx cc t in
Solver.add solver [e1];
(* Solver.push solver; *)
(* let communityInfo = Z3.Expr.mk_const ctx (Symbol.mk_string ctx "communityInfo") string_sort in *)
(* let valueExpr = Z3.Expr.mk_const ctx (Symbol.mk_string ctx "communityInfo.value.cid") string_sort in
let t= Z3.Expr.mk_const ctx  (Symbol.mk_string ctx "cc@trigger.value.cid") string_sort in *)
(* let e2 = Z3.Boolean.mk_eq ctx communityInfo t  in
Solver.add solver [e2]; *)
(* Solver.push solver; *)
let cp = Z3.Expr.mk_const ctx  (Symbol.mk_string ctx "cp") string_sort in
let t = Z3.Expr.mk_const ctx  (Symbol.mk_string ctx "cp@trigger") string_sort in
let e3 = Z3.Boolean.mk_eq ctx cp t in
Solver.add solver [e3];

let newE = Z3.Expr.mk_const ctx (Symbol.mk_string ctx "cc@trigger.value.cid") string_sort in
(* let newB = Z3.Expr.mk_const ctx (Symbol.mk_string  ctx "communityInfo.value.cid") string_sort in *)
let newB = Z3.Expr.mk_const ctx (Symbol.mk_string  ctx "x") string_sort in
let e4 = Z3.Boolean.mk_eq ctx cp newB in

match Z3.Solver.check solver [e4] with
| Z3.Solver.SATISFIABLE -> Printf.printf "Satisfiable\n"; Printf.printf "%s\n" (Z3.Model.to_string (Option.get (Z3.Solver.get_model solver)))
| Z3.Solver.UNSATISFIABLE -> Printf.printf "Unsatisfiable\n"
| Z3.Solver.UNKNOWN -> Printf.printf "Unknown\n"