open Z3;;

(* Context and solver setup *)
let ctx = mk_context [] ;;
let solver = Solver.mk_solver ctx None ;;

(* Declare sorts *)
let string_sort = Seq.mk_string_sort ctx ;;
let int_sort = Arithmetic.Integer.mk_sort ctx ;;
let bool_sort = Boolean.mk_sort ctx ;;
let event_sort = Sort.mk_uninterpreted_s ctx "Event" ;;

(* Recursive function to handle expressions *)
let rec handle_expr ctx solver expr =
  match expr.data with
  | True -> Boolean.mk_true ctx
  | False -> Boolean.mk_false ctx
  | IntLit i -> Arithmetic.Integer.mk_numeral_i ctx i
  | StringLit s -> Seq.mk_string ctx s
  | Parenthesized e -> handle_expr ctx solver e
  | BinaryOp (e1, e2, op) ->
      let left = handle_expr ctx solver e1 in
      let right = handle_expr ctx solver e2 in
      (match op.data with
       | Add -> Arithmetic.mk_add ctx [left; right]
       | Mult -> Arithmetic.mk_mul ctx [left; right]
       | Eq -> Boolean.mk_eq ctx left right
       | NotEq -> Boolean.mk_not ctx (Boolean.mk_eq ctx left right)
       | GreaterThan -> Arithmetic.mk_gt ctx left right
       | LessThan -> Arithmetic.mk_lt ctx left right
       | And -> Boolean.mk_and ctx [left; right]
       | Or -> Boolean.mk_or ctx [left; right])
  | UnaryOp (e, op) ->
      let operand = handle_expr ctx solver e in
      (match op.data with
       | Minus -> Arithmetic.mk_unary_minus ctx operand
       | Negation -> Boolean.mk_not ctx operand)
  | Identifier id -> Expr.mk_const_s ctx id.data string_sort
  | Trigger -> Expr.mk_const_s ctx "trigger" string_sort
  | PropDeref (e, prop) ->
      let base = handle_expr ctx solver e in
      let field = prop.data in
      Expr.mk_app ctx (FuncDecl.mk_func_decl_s ctx field [event_sort] string_sort) [base]
  | List exprs ->
      let expr_values = List.map (handle_expr ctx solver) exprs in
      List.fold_left (fun acc v -> Arithmetic.mk_add ctx [acc; v]) (Arithmetic.mk_numeral_i ctx 0) expr_values
  | Record fields ->
      List.fold_left (fun acc (prop, value) ->
        let field_name = prop.data in
        let field_value = handle_expr ctx solver value in
        Expr.mk_app ctx (FuncDecl.mk_func_decl_s ctx field_name [event_sort] string_sort) [field_value]) (Boolean.mk_true ctx) fields
  | _ -> failwith "Unsupported expression type"

(* Recursively handle events *)
let rec handle_event ctx solver (event : event) =
  let event_id = Expr.mk_const_s ctx event.data.info.data string_sort in
  List.iter (fun sc -> match sc with
    | PlainSC sc -> Solver.add solver [Expr.mk_const_s ctx sc.data string_sort]
    | ParametrisedSC (sc, param) ->
      let param_val = handle_expr ctx solver param in
      let sc_func = FuncDecl.mk_func_decl_s ctx sc.data [string_sort] string_sort in
      Solver.add solver [Boolean.mk_eq ctx (Expr.mk_app ctx sc_func [event_id]) param_val]
  ) event.data.ifc;
  List.iter (fun io -> match io.data with
    | Output expr -> let val_expr = handle_expr ctx solver expr in
      Solver.add solver [Boolean.mk_eq ctx event_id val_expr]
    | _ -> ()) event.data.io

(* Example list of events to handle *)
let events = (* Populate this with your parsed events *)

(* Handle each event *)
List.iter (handle_event ctx solver) events;;

(* Check consistency *)
match Solver.check solver [] with
| SATISFIABLE -> Printf.printf "Satisfiable\n";
                 (match Solver.get_model solver with
                  | Some model -> Printf.printf "Model:\n%s\n" (Model.to_string model)
                  | None -> Printf.printf "No model available\n")
| UNSATISFIABLE -> Printf.printf "Unsatisfiable\n"
| UNKNOWN -> Printf.printf "Unknown\n"
