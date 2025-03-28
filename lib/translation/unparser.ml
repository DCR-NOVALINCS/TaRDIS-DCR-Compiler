(* open Projection.Projections
open Tardis.Syntax.Choreo

let sprintf = Printf.sprintf

and double_quoted ?(quote = "\"") s = quote ^ s ^ quote

let rec babel_unparse (label_types : type_info StringMap.t)
    (ctxt : ProjectionContext.t) =
  let role, _ = ProjectionContext.self ctxt in
  let projection = ProjectionContext.projection ctxt in
  print_endline "\n\n -->";
  print_endline role;
  let babel = generate_projection (label_types, ctxt) projection in
  print_endline babel;
  babel

and generate_projection (label_types, ctxt) (projection : Projection.projection)
    =
  let ({ events; relations } : Projection.projection) = projection in
  List.fold_left
    (fun acc rel -> generate_relation (label_types, ctxt) rel :: acc)
    []
    relations
  |> String.concat "\n" |> String.cat "\n"
  |> String.cat
       (List.fold_left
          (fun acc event -> generate_event (label_types, ctxt) event :: acc)
          []
          events
       |> String.concat "\n")

(* TODO generate participants *)

(* RoleExpr.of("Prosumer", RoleParams.empty()), *)
and generate_userset_expr (label_types, ctxt)
    (constrained_roles : constrained_role StringMap.t) =
  (* TODO a find_first filtered by param name on (either side of) a Positive
     - sort by val-then-sym (since cnf may contemplate both)
     not constrained -> no param; param record otherwise;
     depending on whether it is a user, map to param-records
  *)
  let rec generate_role_params ((_, (params, cnf)) : constrained_role) =
    (* filtered  *)
    List.fold_left
      (fun acc (param_label, _) ->
        let unit_clauses =
          List.filter
            (function
              | [ _ ] -> true
              | _ -> false)
            cnf
          (* TODO map *)
        in
        "" :: acc)
      []
      (StringMap.bindings params)
  (* TODO lookup params - map fully constrained params into record *)
  (* ignore others - attached to events and relations (implicit) *)
  (* if no params -> map to empty param records *)
  and generate_role_expr constrained_role =
    if is_user constrained_role then "" else ""
  in
  (* assert (List.length roles > 0); *)
  List.fold_left
    (fun acc (role, constrained_role) -> "" :: acc)
    []
    (StringMap.bindings constrained_roles)

and generate_event (label_types, ctxt) (event : Projection.event) =
  let uid = double_quoted event.uid
  and id = double_quoted (fst event.info).data
  and label = double_quoted (snd event.info).data
  and communication =
    match event.communication with
    | Projection.Local -> ""
    | Projection.Tx _receivers -> "<TODO Tx expr>"
    | Projection.Rx _initiators -> "<TODO Rx expr>"
  and computation =
    match event.data_expr with
    | Input _ -> ""
    | Computation expr' -> generate_expr (label_types, ctxt) expr'
  and marking =
    match event.data_expr with
    | Input type_expr' ->
      generate_marking (label_types, ctxt) event.marking type_expr'.data
    | Computation expr' ->
      (* print_endline @@ sprintf "%s [%s] : %s"
         event.uid
         (Tardis.Unparser.unparse_expr expr')
         (Tardis.Unparser.unparse_type_expr (annotate (Option.get !(expr'.ty)).t_expr))
         ; *)
      generate_marking
        (label_types, ctxt)
        event.marking
        (Option.get !(expr'.ty)).t_expr
  and cnf_constraint = generate_cnf_constraint (label_types, ctxt) event.self in
  (* print_endline @@ sprintf "Unparsed cnf constraint: %s" cnf_constraint; *)
  match (event.data_expr, event.communication) with
  | Input _, Local ->
    String.concat ", " [ uid; id; label; marking; cnf_constraint ]
    |> sprintf ".addLocalInputEvent(%s)"
  | Input _, Tx _ ->
    String.concat
      ", "
      [ uid; id; label; communication; marking; cnf_constraint ]
    |> sprintf ".addInputEvent(%s)"
  | Computation _, Local ->
    String.concat ", " [ uid; id; label; computation; marking; cnf_constraint ]
    |> sprintf ".addLocalComputationEvent(%s)"
  | Computation _, Tx _ ->
    String.concat
      ", "
      [ uid; id; label; computation; communication; marking; cnf_constraint ]
    |> sprintf ".addComputationEvent(%s)"
  | _, Rx _ ->
    String.concat
      ", "
      [ uid; id; label; communication; marking; cnf_constraint ]
    |> sprintf ".addReceiveEvent(%s)"

(* addControlFlowRelation("03", "e0", "e1",
                    // e0 -->+ e1
                    ControlFlowRelation.Type.RESPONSE) *)
and generate_relation (label_types, ctxt) = function
  | Projection.ControlFlowRelation (uid, src, target, rel_type, self) ->
    let src_uid, src_id = src
    and target_uid, target_id = target
    and rel_type =
      match rel_type with
      | Include -> "ControlFlowRelation.Type.INCLUDE"
      | Exclude -> "ControlFlowRelation.Type.EXCLUDE"
      | Response -> "ControlFlowRelation.Type.RESPONSE"
      | Condition -> "ControlFlowRelation.Type.CONDITION"
      | Milestone -> "ControlFlowRelation.Type.MILESTONE"
    and cnf_constraint = generate_cnf_constraint (label_types, ctxt) self in
    let args = [ uid; src_uid; target_uid; rel_type ] in
    sprintf ".addControlFlowRelation(%s)" @@ String.concat ", " args
  | Projection.SpawnRelation (uid, (_src_uid,src_id), projection) ->
    (* TODO deprecate subgraph element id - no longer required with cnf *)
    let begin_subgraph = sprintf ".beginSpawn(%s, n.a., %s)" uid src_id
    and subgraph = generate_projection (label_types, ctxt) projection
    and end_subgraph = ".endSpawn()" in
    String.concat "\n" [ begin_subgraph; subgraph; end_subgraph ]

(* and relation =
   | ControlFlowRelation of
       (element_uid * event_id)
       * (element_uid * event_id)
       * relation_type
       * constrained_role
   | SpawnRelation of identifier * projection *)

and generate_type_expr (label_types, ctxt) type_expr =
  match type_expr with
  | UnitTy -> "Undefined.ofVoid()"
  | BoolTy -> "BooleanType.singleton()"
  | IntTy -> "IntegerType.singleton()"
  | StringTy -> "GenericStringType.singleton()"
  | RecordTy record_field_tys' ->
    generate_record_type (label_types, ctxt) record_field_tys'
  (* | EventTy of event_ty *)
  | EventRefTy (event_ty, _) -> event_ty
  | _ -> failwith "no-frills demo version - include on a need-to basis"

(* TODO [watch out for updates] in the current version, the parser does not
   consider initial, user-defined, values for events (Babel accounts for the
   possibility, so we translate types directly to their "undefined-value"
   coumterparts) *)
and generate_marking (label_types, ctxt)
    ({ pending; included; _ } : event_marking) ty_expr =
  (* print_endline (Tardis.Unparser.unparse_type_expr (annotate ty_expr)); *)
  (* TODO [post-demo] cover remaining types - restricted to whatever gets us
     the demo for now *)
  let rec generate_undefined_value_of_type = function
    | UnitTy -> "Undefined.ofVoid()"
    | BoolTy -> "BoolVal.undefined()"
    | IntTy -> "IntegerVal.undefined()"
    | StringTy -> "StringVal.undefined()"
    | RecordTy type_fields ->
      generate_record_type (label_types, ctxt) type_fields
      |> sprintf "RecordVal.undefined(%s)"
    | EventTy event_label ->
      ""
      (* let event_type_label = double_quoted event_label
         and { t_expr; _ } =
         StringMap.find event_label label_types in
         let event_type_expr = generate_type_expr (label_types, ctxt) t_expr in
            sprintf "EventVal.undefined(%s, %s)" event_type_label event_type_expr *)
    | EventRefTy (event_label, _) ->
      let type_info = StringMap.find event_label label_types in
      sprintf
        "EventVal.undefined(%s, %s)"
        (double_quoted event_label)
        (generate_type_expr (label_types, ctxt) type_info.t_expr)
    | _ -> failwith "Extend as needed"
  in
  let is_pending = string_of_bool pending.data
  and is_included = string_of_bool included.data
  and default_value = generate_undefined_value_of_type ty_expr in
  sprintf
    "new ImmutableMarkingElement<>(%s, %s, %s)"
    is_pending
    is_included
    default_value

(* TODO [post-demo] map constrained roles to computation expressions inside
   Projection - cnf formulas should not be visible here (encapsulate) *)
and generate_cnf_constraint (label_types, ctxt) constrained_role =
  let open Projection__Sat in
  let rec eq_expr_of expr_1' expr_2' =
    let op = Eq in
    let ty = Some { t_expr = BoolTy; is_const = true } in
    annotate ~ty (BinaryOp (expr_1', expr_2', op))
  and expr_of_cnf_sym_eq sym1 sym2 =
    let expr_1' = cnf_symbol_to_expr sym1
    and expr_2' = cnf_symbol_to_expr sym2 in
    eq_expr_of expr_1' expr_2'
  and expr_of_cnf_eq sym value =
    let expr' = cnf_symbol_to_expr sym
    and val_expr' = cnf_param_val_to_expr value in
    eq_expr_of expr' val_expr'
  and cnf_param_val_to_expr = function
    | BoolLit bool_val ->
      let lit_expr = if bool_val then True else False
      and ty = Some { t_expr = Choreo.BoolTy; is_const = true } in
      annotate ~ty lit_expr
    | IntLit int_val ->
      let expr = Choreo.IntLit int_val
      and ty = Some { t_expr = Choreo.IntTy; is_const = true } in
      annotate ~ty expr
    | StringLit str_val ->
      let expr = Choreo.StringLit str_val
      and ty = Some { t_expr = StringTy; is_const = true } in
      annotate ~ty expr
  (* BinaryOp of expr' * expr' * binary_op_type' *)
  and cnf_symbol_to_expr s1 =
    if String.starts_with ~prefix:"@" s1 then
      (* setup dummy event-ref ty *)
      let ty = Some { t_expr = EventRefTy (s1, true); is_const = true } in
      (* setup dummy event-ref expr *)
      let event_ref_expr' = annotate ~ty (EventRef (annotate s1)) in
      (* setup dummy event-value deref *)
      let sym_expr' = StringMap.find s1 ctxt.trigger_expr_by_symbol in
      let ty = !(sym_expr'.ty) in
      annotate ~ty (PropDeref (event_ref_expr', annotate "value"))
    else (
      print_endline "generating for param id";
      StringMap.find s1 (ctxt.trigger_expr_by_symbol)
(*       
      (* setup dummy event-ref ty *)
      (* TODO const *)
      let ty = Some { t_expr = EventRefTy ("@self", true); is_const = true } in
      (* setup dummy event-ref expr *)
      let event_ref_expr' = annotate ~ty (EventRef (annotate "@self")) in
      (* setup dummy event-value deref *)
      let sym_expr' = StringMap.find s1 ctxt.trigger_expr_by_symbol in
      let ty = !(sym_expr'.ty) in
      let prop_deref' = annotate ~ty (PropDeref (event_ref_expr', annotate "value")) in
      let _, (params, _) = constrained_role in
      let field = List.hd (List.tl (String.split_on_char '#' s1)) in
      let ty = Some {t_expr=StringMap.find field params; is_const=true} in
      annotate ~ty (PropDeref (prop_deref', annotate field)) *)

    )
  (* generate_expr (label_types, ctxt) value_deref_expr *)
  (* and param_val_to_expr = function
     | BoolLit bool_lit ->
       generate_literal_expr (if bool_lit then Choreo.True else Choreo.False)
     | IntLit int_lit -> generate_literal_expr (Choreo.IntLit int_lit)
     | StringLit str_lit -> generate_literal_expr (Choreo.StringLit str_lit) *)
  and cnf_bool_constraint_to_expr = function
    | CnfSymEq (s1, s2) ->
      (* create 'dummy' events after symbol names *)
      let expr' = expr_of_cnf_sym_eq s1 s2 in
      (* print_endline
         @@ sprintf "CnfEqExpr generated: %s" (Tardis.Unparser.unparse_expr expr'); *)
      expr'
    | CnfEq (s, value) ->
      let expr' = expr_of_cnf_eq s value in
      (* print_endline
         @@ sprintf "CnfEqExpr generated: %s" (Tardis.Unparser.unparse_expr expr'); *)
      expr'
  and cnf_lit_to_expr = function
    | Positive lit -> cnf_bool_constraint_to_expr lit
    | Negative lit ->
      (* TODO *)
      let eq_expr' = cnf_bool_constraint_to_expr lit in
      let ty = !(eq_expr'.ty) in
      annotate ~ty (UnaryOp (eq_expr', Negation))
  and cnf_clause_to_expr clause =
    (* TODO revisit const *)
    let ty = Some { t_expr = BoolTy; is_const = true } in
    List.fold_left
      (fun expr1' clause ->
        annotate ~ty (BinaryOp (expr1', cnf_lit_to_expr clause, Or)))
      (annotate ~ty True)
      clause
  (* let generate_of_clause (clause:Projection__Sat.cnf_clause) =
       List.fold_left ( l r -> ) clause
     in *)
  and cnf_formula_to_expr (cnf : Projection__Sat.cnf_formula) =
    let ty = Some { t_expr = BoolTy; is_const = true } in
    List.fold_left
      (fun expr1' cnf_clause ->
        annotate ~ty (BinaryOp (expr1', cnf_clause_to_expr cnf_clause, And)))
      (annotate ~ty True)
      cnf
  in
  let generate_instantiation_guard_expr (cnf : Projection__Sat.cnf_formula) =
    match cnf with
    | [] -> "BooleanLiteral.of(true)"
    | _ -> generate_expr (label_types, ctxt) @@ cnf_formula_to_expr cnf
  in
  let _, (_, cnf) = constrained_role in
  generate_instantiation_guard_expr cnf

(*
   add<type>Event
*)

(* literal expr - an expression based on a single primitive literal
   (bool, int, string) *)
and generate_literal_expr = function
  | True -> sprintf "BooleanLiteral.of(true)"
  | False -> sprintf "BooleanLiteral.of(false)"
  | IntLit int_val -> sprintf "IntegerLiteral.of(%s)" (string_of_int int_val)
  | StringLit str_val -> sprintf "StringLiteral.of(%s)" (double_quoted str_val)
  | _ -> failwith "Not a literal-expr"

(*
   <pattern>
   Record.Field.of("field_name", <field_value>)
*)
and generate_record_field :
      'a. ('a -> string) -> (identifier' * 'a annotated) annotated -> string =
 fun field_unparser field' ->
  let name', field' = field'.data in
  let field_name = double_quoted name'.data
  and field_val = field_unparser field'.data in
  sprintf "Record.Field.of(%s,%s)" field_name field_val

(*
   <pattern>
     Record.ofEntries(
       Record.Field.of("field_name_1", <field_val_1>),
       Record.Field.of("field_name_2", <field_val_2>),
       ...
     )
*)
and generate_record_fields :
      'a.
      ('a -> string) -> (identifier' * 'a annotated) annotated list -> string =
 fun field_unparser fields ->
  List.fold_left
    (fun acc field -> generate_record_field field_unparser field :: acc)
    []
    fields
  |> String.concat ","
  |> sprintf "Record.ofEntries(%s)"

(*
  TODO [post-demo] cover remaining types - restricted to whatever gets us
  the demo for now

  <pattern>
  RecordType.of(
    Record.ofEntries(
      Record.Field.of("field_name_1", BooleanT.of(true),
      Record.Field.of("field_name_2", IntegerLiteral.of(2)),
      Record.Field.of("field_name_3", StringLiteral.of('time_slot')),
      ...
    )
  )
*)
and generate_record_type (label_types, ctxt) (fields : record_field_ty' list) =
  generate_record_fields (generate_type_expr (label_types, ctxt)) fields
  |> sprintf "RecordType.of(%s)"

(* and generate_undefined_record_val (fields : record_field_ty' list) =
   generate_record_type fields
   |> sprintf "RecordVal.undefined(%s)" *)

(*
   TODO [after-demo] include all exprs - Bools, Ints and Strings gets us the
   demo (?) (minimum-effort)

    <pattern>
    RecordExpr.of(
      Record.ofEntries(
        Record.Field.of("field_name_1", BooleanType.singleton(),
        Record.Field.of("field_name_2", IntegerType.singleton(),
        Record.Field.of("field_name_3", GenericStringType.singleton(),
        ...
      )
    )
*)
and generate_record_expr (label_types, ctxt) (fields : record_field' list) =
  generate_record_fields generate_literal_expr fields
  |> sprintf "RecordExpr.of(%s)"

(*
  <pattern>
  RecordFieldDeref.of(
    EventValueDeref.of(
      EventIdExpr.of(
        EventIdVal.of("e1",
          EventType.of("E1",
            RecordType.of(
              Record.ofEntries(
                Record.Field.of("kw", IntegerType.singleton()),
                Record.Field.of("t", IntegerType.singleton())
    ) ) ) ) ) ),
    "kw"
  )
*)
(* and generate_prop_deref_expr (label_types, ctxt)
     ((expr', prop_name') : expr' * property_name') =
   (* print_endline (Tardis.Unparser.unparse_expr expr'); *)
   (* typechecker assumed to have set this  *)
   let type_expr' = (Option.get !(expr'.ty)).t_expr in
   match (expr'.data, (Option.get !(expr'.ty)).t_expr) with
   | Record expr_fields, RecordTy ty_fields ->
     let record_expr = generate_record_expr (label_types, ctxt) expr_fields in
     sprintf "RecordFieldDeref.of(%s,%s)" record_expr prop_name'.data
   | PropDeref (nested_expr', nested_property'), type_expr -> ""
   | EventRef event_id', EventRefTy (event_label, _) ->
     sprintf "EventValueDeref.of(%s)" "TODO1"
   | _ -> failwith "internal error: should not have passed typechecking!" *)

and generate_expr (label_types, ctxt) (expr' : expr') =
  let rec self_to_record_ty () =
    let to_type_info type_expr =
      Some { t_expr = type_expr; is_const = true }
    in
    let role_label, (params, _) = ProjectionContext.self ctxt in
    let record_ty_info =
      List.map
        (fun (param_name, param_ty) ->
          let named_param' = annotate param_name
          and type_info_opt = to_type_info param_ty in
          let type_expr' = annotate ~ty:type_info_opt param_ty in
          annotate ~ty:type_info_opt (named_param', type_expr'))
        (StringMap.bindings params)
    in   
   {t_expr=RecordTy record_ty_info; is_const=true}
  in
  let rec generate_prop_deref_helper t_expr (expr', prop_name') =
    match expr'.data with
    | PropDeref (expr_1', prop_name_1') -> begin
      match prop_name'.data with
      | "value" ->
        sprintf
          "EventValueDeref.of(%s)"
          (generate_prop_deref_helper t_expr (expr_1', prop_name_1'))
      | field ->
        sprintf
          "RecordFieldDeref.of(%s,%s)"
          (generate_prop_deref_helper t_expr (expr_1', prop_name_1'))
          (double_quoted field)
    end
    | EventRef label' ->
      sprintf
        "EventValueDeref.of(%s)"
        (generate_expr (label_types, ctxt) expr')
        (* (double_quoted label'.data)
        (generate_type_expr (label_types, ctxt) t_expr) *)
    | Trigger label ->
      sprintf "EventValueDeref.of(%s)"
        (generate_expr (label_types, ctxt) expr')
      (* sprintf
        "EventValueDeref.of(EventIdExpr.of(EventIdVal.of(%s,%s)))"
        (double_quoted label)
        (generate_type_expr (label_types, ctxt) t_expr) *)
    | Record _ ->
      failwith "Record expr directly in prop-deref - not yet implemented"
    | _ -> failwith "unsupported expr in prop-deref"
  in
  match expr'.data with
  | True | False | IntLit _ | StringLit _ -> generate_literal_expr expr'.data
  | Record record_fields ->
    generate_record_expr (label_types, ctxt) record_fields
  | PropDeref (expr', prop_name') ->
    let t_expr = (Option.get !(expr'.ty)).t_expr in
    print_endline
    @@ sprintf
         "expr %s has t_expr is %s for prop %s"
         (Tardis.Unparser.unparse_expr expr')
         (Tardis.Unparser.unparse_type_expr (annotate t_expr))
         prop_name'.data;
    let str = generate_prop_deref_helper t_expr (expr', prop_name') in
    print_endline @@ sprintf "prop-deref helper returning: %s" str;
    str
  | EventRef event_id' -> begin
    match (Option.get !(expr'.ty)).t_expr with
    | EventRefTy (event_label, _) ->
      print_endline @@ sprintf ">>> event label: %s" event_label;

      (* TODO clean this up - temporary workaround to not having @self in
      the label environment *)
      let type_info = if String.starts_with ~prefix:"@self" event_label then self_to_record_ty () else (
      (* note: @this point we're mixing actual events with dummy events created
         for the purpose of representing symbols - so we must lookup
         events in two places - TODO when the solution stabilizes,
          this must be  handled better *)
      (* let type_info = StringMap.find event_label label_types in *)
      print_endline @@ sprintf "Looking for event %s" event_label;
         List.iter (
           fun (k,v) ->
             print_endline @@ sprintf " (%s , %s) "
             (k)
             (Tardis.Unparser.unparse_expr v)
           ) (StringMap.bindings ctxt.trigger_expr_by_symbol);
      
        Option.fold
          ~none:
            (let sym_expr' =
               StringMap.find event_label ctxt.trigger_expr_by_symbol
             in
             Option.get !(sym_expr'.ty))
          ~some:Fun.id
          (StringMap.find_opt event_label label_types)
      )
      in
      sprintf
        "EventIdExpr.of(EventIdVal.of(%s,EventType.of(%s, %s)))"
        (double_quoted event_id'.data)
        (double_quoted event_label)
        (generate_type_expr (label_types, ctxt) type_info.t_expr)
    | _ -> failwith "Should not have passed typechecking"
  end
  | BinaryOp (expr1', expr2', op) ->
    let op_of =
      begin
        match op with
        | Eq -> sprintf "EqualsExpr.of(%s, %s)"
        | And -> sprintf "LogicalOpExpr.and(%s, %s)"
        | Or -> sprintf "LogicalOpExpr.or(%s, %s)"
        | _ -> failwith "Not implemented: generate binary ops as needed."
      end
    in
    op_of
      (generate_expr (label_types, ctxt) expr1')
      (generate_expr (label_types, ctxt) expr2')
  | UnaryOp (expr', op) ->
    let op =
      begin
        match op with
        | Negation -> sprintf "NegationExpr.of(%s)"
        | _ -> failwith "Not implemented: generate unary ops as needed."
      end
    in
    op (generate_expr (label_types, ctxt) expr')
  (* generate_prop_deref_expr (label_types, ctxt) (expr', property_name) *)
  (* | need AND/OR expressions for expressing CNF constraints *)
  (* | need @trigger expressions for expressing CNF constraints *)
  | Trigger _ -> 
    (* TODO
    find in environment
    *)
    
    failwith "Trigger not implemented"
  | _ -> failwith "Not implemented" *)
