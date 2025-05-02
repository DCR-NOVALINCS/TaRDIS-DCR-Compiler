open Syntax

let sprintf = Printf.sprintf

let string_escape s = "\"" ^ s ^ "\""

let string_escape' s = "'" ^ s ^ "'"

let rec unparse_prog ?(indent = "") ?(abbreviated = true)
    ({ roles; security_lattice; spawn_program } : program) =
  unparse_value_dep_role_decls roles
  ^ "\n;\n\n"
  ^ unparse_lattice_flow_decls security_lattice
  ^ "\n;\n\n"
  ^ unparse_spawn_prog indent abbreviated spawn_program

and unparse_spawn_prog indent abbreviated { events; relations } =
  (* let events, ctrl_rels = spawn_program in *)
  unparse_events indent abbreviated events
  ^
  if relations == [] then ""
  else "\n" ^ unparse_relations indent abbreviated relations

(* Ancillary - common - move upwards *)
and unparse_parametrisable_label param_unparser param_label =
  let named_param_unparser param' =
    let param_name', param_val' = param'.data in
    Printf.sprintf "%s:%s" param_name'.data @@ param_unparser param_val'
  and label, params = param_label.data in
  Printf.sprintf "%s(%s)" label.data
  @@ String.concat "; "
  @@ List.map named_param_unparser params

and unparse_value_dep_role_decls decls =
  String.concat "\n"
  @@ List.map (unparse_parametrisable_label unparse_type_expr) decls
(*
   and unparse_security_level_decls level_decls =
     let unparse_security_level_decl decl =
       match decl.data with
       | PlainSCDecl role -> role.data
       | ParametrisedSCDecl (role, param_type) ->
         let unparsed_param_types = unparse_type' param_type.data in
         role.data ^ "(" ^ unparsed_param_types ^ ")"
     in
     String.concat "\n" @@ List.map unparse_security_level_decl level_decls *)

and unparse_lattice_flow_decls flow_decls =
  let unparse_lattice_flow_decl { data = l1, l2; _ } =
    l1.data ^ " flows " ^ l2.data
  in
  let unparsed_lattice_flow_decls =
    List.map unparse_lattice_flow_decl flow_decls
  in
  String.concat "\n" unparsed_lattice_flow_decls

and unparse_value' value' = unparse_value value'.data

and unparse_value = function
  | BoolVal bool_val -> Bool.to_string bool_val
  | IntVal int_val -> Int.to_string int_val
  | StringVal string_val -> string_val
  | RecordVal record_fields ->
    List.map
      (fun field' ->
        let name', value' = field'.data in
        sprintf "%s=%s" name'.data (unparse_value' value'))
      record_fields
    |> String.concat ", " |> sprintf "{%s}"

and unparse_type_expr ty = unparse_type ty.data

and unparse_type type_expr =
  match type_expr with
  | UnitTy -> "Unit"
  | StringTy -> "String"
  | IntTy -> "Integer"
  | BoolTy -> "Boolean"
  | EventTy event_id -> event_id
  | EventRefTy (event_label, is_ref_to_const) ->
    Printf.sprintf
      "%s %s"
      (if is_ref_to_const then "(const)" else "")
      event_label
  | RecordTy type_fields ->
    let unparse_type_field type_field =
      let name, type_value = type_field.data in
      name.data ^ ":" ^ unparse_type type_value.data
    in
    let unparsed_type_fields =
      String.concat ", " @@ List.map unparse_type_field type_fields
    in
    "{" ^ unparsed_type_fields ^ "}"
  | ListTy t ->
    let ty = t in
    "List(" ^ unparse_type ty ^ ")"
  | ListTyEmpty -> "List()"

and unparse_binary_op_type op' =
  match op' with
  | Add -> "+"
  | Mult -> "*"
  | Eq -> "="
  | NotEq -> "!="
  | GreaterThan -> ">"
  | LessThan -> "<"
  | And -> "AND"
  | Or -> "OR"

and unparse_unary_op_type op' =
  match op' with
  | Minus -> "-"
  | Negation -> "~"

(* TODO [revise] quote here is a code smell *)
and unparse_expr ?(quote = "'") { data = e; _ } =
  let unparse_expr' = unparse_expr ~quote in
  match e with
  | True -> "true"
  | False -> "false"
  | IntLit n -> string_of_int n
  | StringLit s -> quote ^ s ^ quote
  | BinaryOp (e1, e2, op_type') ->
    unparse_expr e1 ^ " "
    ^ unparse_binary_op_type op_type'
    ^ " " ^ unparse_expr e2
  | UnaryOp (e, op_type') -> unparse_unary_op_type op_type' ^ unparse_expr e
  | Parenthesized e1 -> "(" ^ unparse_expr' e1 ^ ")"
  | EventRef s -> s.data
  (* | Trigger -> "@trigger" *)
  | Trigger label -> label
  | PropDeref (e1, s) -> unparse_expr' e1 ^ "." ^ s.data
  | List elements ->
    let unparsed_elements = List.map (unparse_expr ~quote) elements in
    String.concat ", " unparsed_elements
  | Record record_fields ->
    let unparse_record_field (name, value) =
      name.data ^ ": " ^ unparse_expr ~quote value
    in
    let unparsed_fields =
      String.concat ", "
      @@ List.map unparse_record_field (deannotate_list record_fields)
    in
    "{" ^ unparsed_fields ^ "}"

and unparse_event_info (id, label) = "(" ^ id.data ^ ":" ^ label.data ^ ")"

(* TODO factor constants out *)
and unparse_sec_label_param_val' = function
  | Top -> "Top"
  | Bot -> "Bot"
  | Parameterised expr -> unparse_expr expr

and unparse_sec_label_param' (id, value) =
  Printf.sprintf "(%s:%s)" id.data @@ unparse_sec_label_param_val' value.data

and unparse_sec_label' = function
  | role, [] -> role.data
  | role, named_params ->
    deannotate_list named_params
    |> List.map unparse_sec_label_param'
    |> String.concat ";"
    |> Printf.sprintf "%s(%s)" role.data

and unparse_security_level' sec_labels =
  deannotate_list sec_labels
  |> List.map unparse_sec_label'
  |> String.concat "," |> Printf.sprintf "(%s)"

and unparse_event_io io' =
  begin
    match io' with
    | Input inputType -> begin
      match inputType.data with
      | UnitTy -> "[?]"
      | _ -> "[? : " ^ unparse_type inputType.data ^ "]"
    end
    | Computation computationExpr -> "[" ^ unparse_expr computationExpr ^ "]"
  end

and unparse_event_marking_as_prefix marking' =
  let { is_pending'; is_included'; _ } = marking' in
  begin
    match (is_pending'.data, is_included'.data) with
    | true, false -> "!%"
    | true, true -> "!"
    | false, true -> ""
    | false, false -> "%"
  end

and unparse_user_set_param param' =
  let name', value' = param'.data in
  match value'.data with
  | Expr expr' -> Printf.sprintf "%s=%s" name'.data (unparse_expr expr')
  | Alias identifier' -> Printf.sprintf "%s=@%s" name'.data identifier'.data
  | Any -> Printf.sprintf "%s=*" name'.data
  | RuntimeValue alias_opt' -> begin
    match alias_opt' with
    | Some alias' -> Printf.sprintf "#%s as %s" name'.data alias'.data
    | None -> Printf.sprintf "#%s" name'.data
  end

and unparse_user_set_expr = function
  | RoleExpr role_expr' ->
    let role', params = role_expr'.data in
    List.map unparse_user_set_param params
    |> String.concat "; "
    |> Printf.sprintf "%s(%s)" role'.data
  | Initiator event_id' -> Printf.sprintf "@Initiator(%s)" event_id'.data
  | Receiver event_id' -> Printf.sprintf "@Receiver(%s)" event_id'.data

and unparse_user_set_exprs user_set_exprs =
  List.map unparse_user_set_expr (deannotate_list user_set_exprs)
  |> String.concat ", "

and unparse_event_participants participants' =
  match participants'.data with
  | Local initiator' -> unparse_user_set_expr initiator'.data
  | Interaction (initiator', receivers) ->
    List.map unparse_user_set_expr (deannotate_list receivers)
    |> String.concat ", "
    |> Printf.sprintf "%s -> %s" (unparse_user_set_expr initiator'.data)

and unparse_event_marking_extended { is_pending'; is_included'; default_val } =
  let default_val =
    Option.fold default_val ~none:String.empty ~some:(fun value' ->
        unparse_value' value')
  in
  let short_string_of_bool bool_val = if bool_val then "T" else "F" in
  let pend = short_string_of_bool is_pending'.data in
  let inc = short_string_of_bool is_included'.data in
  Printf.sprintf "{pe:%s; in:%s; default:%s}" pend inc default_val

and unparse_events indent abbreviated events =
  let unparse_event event' =
    let buf = Buffer.create 32 in

    let event = event'.data in
    let info', _sec_level = (event.info, event.security_level) in
    Buffer.add_string buf @@ indent;
    if abbreviated then
      Buffer.add_string buf
      @@ unparse_event_marking_as_prefix event.marking.data;
    Buffer.add_string buf @@ unparse_event_info info'.data;
    Buffer.add_string buf @@ " "
    ^ unparse_security_level' event.security_level.data;
    Buffer.add_string buf @@ " " ^ unparse_event_io event.data_expr.data;
    Buffer.add_string buf @@ " [ "
    ^ unparse_event_participants event.participants
    ^ " ]";
    if not abbreviated then
      Buffer.add_string buf @@ "   "
      ^ unparse_event_marking_extended event.marking.data;
    Buffer.contents buf
  in
  let unparsed_events = List.map unparse_event events in
  String.concat "\n" unparsed_events

and unparse_guard_expr guard_expr' =
  match guard_expr'.data with
  | True -> ""
  | _ -> Printf.sprintf "[ %s ]" @@ unparse_expr guard_expr'

and unparse_ctrl_flow_relation_type ?(guard_expr = annotate True) = function
  | Condition -> Printf.sprintf "-%s->*" (unparse_guard_expr guard_expr)
  | Response -> Printf.sprintf "*-%s->" (unparse_guard_expr guard_expr)
  | Include -> Printf.sprintf "-%s->+" (unparse_guard_expr guard_expr)
  | Exclude -> Printf.sprintf "-%s->%%" (unparse_guard_expr guard_expr)
  | Milestone -> Printf.sprintf "-%s-><>" (unparse_guard_expr guard_expr)

(*  TODO refactor with unparse_ctrl_flow_relation_type (added for another purpose) *)
and unparse_ctrl_relation indent _abbreviated id1 guard_expr id2 rel_type' =
  let id1', id2' = (id1.data, id2.data) in
  let unparsed_guard = unparse_guard_expr guard_expr in
  let unparsed_rel =
    match rel_type'.data with
    | Condition -> Printf.sprintf "%s -%s->* %s" id1' unparsed_guard id2'
    | Response -> Printf.sprintf "%s *-%s-> %s" id1' unparsed_guard id2'
    | Include -> Printf.sprintf "%s -%s->+ %s" id1' unparsed_guard id2'
    | Exclude -> Printf.sprintf "%s -%s->%% %s" id1' unparsed_guard id2'
    | Milestone -> Printf.sprintf "%s -%s-><> %s" id1' unparsed_guard id2'
  in
  indent ^ unparsed_rel

and unparse_spawn_relation indent abbreviated id guard_expr spawn_program =
  let id' = id.data in
  let increased_indent = indent ^ "\t" in
  let unparsed_guard = unparse_guard_expr guard_expr in
  let unparsed_spawn_prog =
    unparse_spawn_prog increased_indent abbreviated spawn_program
  in
  indent
  ^ Printf.sprintf "%s -%s->> {\n%s\n" id' unparsed_guard unparsed_spawn_prog
  ^ indent ^ "}"

and unparse_relations indent abbreviated ctrl_rels =
  let unparse_rel ctrl_rel =
    match ctrl_rel.data with
    | ControlRelation (id1, guard_expr, id2, rel_type) ->
      unparse_ctrl_relation indent abbreviated id1 guard_expr id2 rel_type
    | SpawnRelation (id, _, guard_expr, spawn_program) ->
      unparse_spawn_relation indent abbreviated id guard_expr spawn_program
  in
  let unparsed_rels = List.map unparse_rel ctrl_rels in
  indent ^ ";\n\n" ^ String.concat "\n" unparsed_rels
