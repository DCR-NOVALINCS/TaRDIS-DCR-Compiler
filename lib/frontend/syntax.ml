(* Naming Convention: we use <id>' for annotated AST nodes *)

  type loc =
    | Nowhere
    | Location of Lexing.position * Lexing.position

  and 'a annotated =
    { data : 'a
    ; loc : loc
    ; uid : string option ref
    ; ty : type_info option ref
    ; ifc: bool option ref
    }

  and type_info =
    { t_expr : type_expr
    ; is_const : bool
    }

  (* AST nodes are annotated *)

  (* generic identifier *)
  and identifier' = identifier annotated

  and identifier = string

  and element_uid = identifier

  (*
    =============================================================================
    Expressions & Type Expressions
    =============================================================================
  *)
  and type_expr' = type_expr annotated

  and event_ty = identifier

  and type_expr =
    | UnitTy
    | StringTy
    | IntTy
    | BoolTy
    | EventTy of event_ty
    (* TODO [revise way how this is used - for typing only, not parsing] *)
    | EventRefTy of event_ty * bool
    | RecordTy of record_field_ty' list
    (* TODO remove *)
    | ListTy of type_expr
    | ListTyEmpty

  and record_field_ty' = type_expr' named_param'

  and expr' = expr annotated

  and expr =
    | True
    | False
    | IntLit of int
    | StringLit of string
    | Parenthesized of expr'
    | BinaryOp of expr' * expr' * binary_op_type
    | UnaryOp of expr' * unary_op_type
    | EventRef of identifier'
    | Trigger of string
    | PropDeref of expr' * property_name'
    | List of expr' list
    | Record of record_field' list

  and binary_op' = binary_op annotated

  and binary_op = expr' * expr' * binary_op_type

  and binary_op_type =
    | Add
    | Mult
    | Eq
    | NotEq
    | GreaterThan
    | LessThan
    | And
    | Or

  and unary_op' = unary_op annotated

  and unary_op = expr' * unary_op_type

  and unary_op_type =
    | Minus
    | Negation

  and record_field' = record_field annotated

  and record_field = property_name' * expr'

  and property_name' = string annotated

  (*
    =============================================================================
    Parameterisable Roles
    =============================================================================
  *)

  (* a generic tuple for named properties, fields, parameters,...  *)
  and 'a named_param' = 'a named_param annotated

  and 'a named_param = identifier' * 'a

  and role_label' = role_label annotated

  and role_label = identifier

  (* generic type for "value-dependent label" expressions *)
  and 'a parameterisable_role' = 'a parameterisable_role annotated

  and 'a parameterisable_role = role_label' * 'a named_param' list

  (*
    =============================================================================
    =============================================================================
    Program
    =============================================================================
    =============================================================================
  *)
  and program =
    { roles : value_dep_role_decl' list
    ; security_lattice : flow_relation' list
    ; spawn_program : spawn_program
    }

  and spawn_program =
    { events : event' list
    ; relations : relation' list
    }

  (*
    program.roles 
    --------------------------------------
  *)
  and value_dep_role_decl' = type_expr' parameterisable_role'

  (*
    program.security_lattice
    --------------------------------------
  *)
  and flow_relation' = flow_relation annotated

  and flow_relation = role_label' * role_label'

  (*
    program.events
    --------------------------------------
  *)
  and event' = event annotated

  and event =
    { info : event_info'
    ; security_level : security_level'
    ; data_expr : data_expr'
    ; participants : participants'
    ; marking : event_marking'
    }

  (*
    program.relations
    --------------------------------------
  *)
  and relation' = relation annotated

  and relation =
    | ControlRelation of event_id' * expr' * event_id' * relation_type'
    | SpawnRelation of event_id' * identifier * expr' * spawn_program

  (*
    =============================================================================
    Event
    =============================================================================
  *)
  and event_id' = event_id annotated

  and event_id = identifier

  and event_label' = event_label annotated

  and event_label = identifier

  (*
    event.info
    --------------------------------------
  *)
  and event_info' = event_info annotated

  and event_info = event_id' * event_label'

  (*
    --------------------------------------
    event.security_level
    --------------------------------------
  *)
  and parametrisable_label_decls' = parametrisable_label_decls annotated

  and parametrisable_label_decls = expr' list

  and sec_label_param' = sec_label_param annotated

  and sec_label_param =
    | Top
    (* e.g., Buyer(Bot) *)
    | Bot
    (* e.g., Buyer(id) *)
    | Parameterised of expr'

  and sec_label' = sec_label_param' parameterisable_role'

  and security_level' = security_level annotated

  and security_level = sec_label' list

  (*
    event.data_expr
    --------------------------------------
  *)
  and data_expr' = data_expr annotated

  and data_expr =
    | Input of type_expr'
    | Computation of expr'

  (*
    event.participants
    --------------------------------------
  *)
  and user_set_param_val' = user_set_param_val annotated

  and user_set_param_val =
    | Expr of expr'
    | Alias of identifier'
    | Any
    | RuntimeValue of identifier' option

  and userset_role_expr' = user_set_param_val' parameterisable_role'

  and user_set_expr' = user_set_expr annotated

  and user_set_expr =
    | RoleExpr of userset_role_expr'
    | Initiator of event_id'
    | Receiver of event_id'
    (* | Diff of user_set_expr' list * user_set_expr' list *)


  and participants' = participants annotated

  and participants =
    | Local of user_set_expr'
    | Interaction of user_set_expr' * user_set_expr' list

  (*
    event.marking
    --------------------------------------
  *)
  and event_marking' = event_marking annotated

  and event_marking =
    { executed' : bool annotated
    ; pending' : bool annotated
    ; included' : bool annotated
    }

  (*
    =============================================================================
    Relation
    =============================================================================
  *)
  and relation_type' = relation_type annotated

  and relation_type =
    | Condition
    | Include
    | Exclude
    | Milestone
    | Response

  (* TODO move somewhere else - debug/log/print *)
  let string_of_pos (pos : Lexing.position) =
    "line "
    ^ string_of_int pos.Lexing.pos_lnum
    ^ ", character "
    ^ string_of_int (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)

  (* TODO move somewhere else - debug/log/print *)
  let string_of_loc loc =
    begin
      match loc with
      | Nowhere -> "?"
      | Location (p1, _) -> string_of_pos p1
    end

  let annotate ?(loc = Nowhere) ?(ty = None) ?(uid = None) ?(ifc = None) n =
    { data = n; loc; uid = ref uid; ty = ref ty; ifc = ref ifc }

  let deannotate a = a.data

  let deannotate_list (l : 'a annotated list) = List.map deannotate l
