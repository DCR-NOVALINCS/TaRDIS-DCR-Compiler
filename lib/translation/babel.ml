open Endpoint_projection.Endpoint
open Yojson

let rec encode_value' (value' : value') = encode_value value'.data

and encode_value (value : value) =
  match value with
  | BoolVal bool_val ->
    `Assoc [ ("value", `Bool bool_val) ] |> fun value ->
    `Assoc [ ("boolLit", value) ]
  | IntVal int_val ->
    `Assoc [ ("value", `Int int_val) ] |> fun value ->
    `Assoc [ ("intLit", value) ]
  | StringVal string_val ->
    `Assoc [ ("value", `String string_val) ] |> fun value ->
    `Assoc [ ("stringLit", value) ]
  | RecordVal fields ->
    List.fold_left
      (fun (acc : Basic.t list) (field' : record_field_val') ->
        let name', value' = field'.data in
        let field_name = ("name", `String name'.data)
        and field_value = ("value", encode_value' value') in
        `Assoc [ field_name; field_value ] :: acc)
      []
      fields
    |> fun lst ->
    `Assoc [ ("fields", `List (List.rev lst)) ] |> fun rec_val ->
    `Assoc [ ("recordVal", rec_val) ]

and encode_type_expr (type_expr : Choreo.type_expr) : Basic.t =
  match type_expr with
  | Choreo.UnitTy -> `Assoc [ ("valueType", `String "void") ]
  | Choreo.BoolTy -> `Assoc [ ("valueType", `String "bool") ]
  | Choreo.IntTy -> `Assoc [ ("valueType", `String "int") ]
  | Choreo.StringTy -> `Assoc [ ("valueType", `String "string") ]
  | Choreo.EventRefTy (label, _) -> `Assoc [ ("label", `String label) ]
  | Choreo.RecordTy ty_fields ->
    List.fold_left
      (fun (assoc_list : Basic.t list)
           ((name', type_expr') : Choreo.identifier' * Choreo.type_expr')
         ->
        `Assoc
          [ ("name", `String name'.data)
          ; ("type", encode_type_expr' type_expr')
          ]
        :: assoc_list)
      []
      (Choreo.deannotate_list ty_fields)
    |> fun (type_fields : Basic.t list) ->
    `Assoc [ ("recordType", `Assoc [ ("fields", `List type_fields) ]) ]
  | _ -> assert false

and encode_type_expr' (type_expr' : Choreo.type_expr') : Basic.t =
  match type_expr'.data with
  | Choreo.EventTy _ ->
    let ty = (Option.get !(type_expr'.ty)).t_expr in
    `Assoc [ ("eventType", encode_type_expr ty) ]
  | _ -> encode_type_expr type_expr'.data

and encode_expr' (expr' : expr') = encode_expr expr'.data

and encode_expr (expr : expr) =
  match expr with
  | True -> `Assoc [ ("boolLit", `Assoc [ ("value", `Bool true) ]) ]
  | False -> `Assoc [ ("boolLit", `Assoc [ ("value", `Bool false) ]) ]
  | IntLit int_val -> `Assoc [ ("intLit", `Assoc [ ("value", `Int int_val) ]) ]
  | StringLit string_val ->
    `Assoc [ ("stringLit", `Assoc [ ("value", `String string_val) ]) ]
  | EventRef label' ->
    `Assoc [ ("eventRef", `Assoc [ ("value", `String label'.data) ]) ]
  | Trigger label ->
    `Assoc [ ("eventRef", `Assoc [ ("value", `String label) ]) ]
  | Record fields ->
    List.map
      (fun (field' : record_field_expr') ->
        let name', value' = field'.data in
        let name = ("name", `String name'.data)
        and value = ("value", encode_expr' value') in
        `Assoc [ name; value ])
      fields
    |> fun (fields : Basic.t list) ->
    `Assoc [ ("record", `Assoc [ ("fields", `List fields) ]) ]
  | PropDeref (expr', prop') ->
    let prop_based_expr = ("propBasedExpr", encode_expr' expr')
    and prop = ("prop", `String prop'.data) in
    `Assoc [ ("propDeref", `Assoc [ prop_based_expr; prop ]) ]
  | BinaryOp (expr1', expr2', op) ->
    let expr1 = ("expr1", encode_expr' expr1')
    and expr2 = ("expr2", encode_expr' expr2') in
    let encode_binary_op op =
      `Assoc [ ("binaryOp", `Assoc [ expr1; expr2; ("op", `String op) ]) ]
    in
    (* assumption: at this point of the pipeline, expr1 and expr2 have the 
    same type (previously convert to the LUB-type if necessary) *)
    let operand_type = (Option.get !(expr1'.ty)).t_expr in
    begin
      match op with
      | And -> encode_binary_op "and"
      | Or -> encode_binary_op "or"
      | Eq -> encode_binary_op "equals"
      | NotEq -> encode_binary_op "notEquals"
      | Add ->
        encode_binary_op
          begin
            match operand_type with
            | IntTy -> "intAdd"
            | StringTy -> "stringConcat"
            | _ ->
              (* the operator does not apply to further types (extend as needed) *)
              assert false
          end
      | LessThan ->
        encode_binary_op
          begin
            match operand_type with
            | IntTy -> "intLessThan"
            | _ ->
              (* the operator does not apply to further types (extend as needed) *)
              assert false
          end
      | GreaterThan ->
        encode_binary_op
          begin
            match operand_type with
            | IntTy -> "intGreaterThan"
            | _ ->
              (* the operator does not apply to further types (extend as needed) *)
              assert false
          end
      | _ ->
        (* TODO encode remaining exprs *)
        assert false
    end
  | _ -> assert false

and encode_data_expr' (data_expr' : Choreo.data_expr') =
  encode_data_expr data_expr'.data

and encode_data_expr (data_expr : Choreo.data_expr) : Basic.t =
  match data_expr with
  | Choreo.Input type_expr' -> encode_type_expr' type_expr'
  | Choreo.Computation expr' -> encode_expr' expr'

and encode_user_set_expr' (user_set_expr' : user_set_expr') =
  encode_user_set_expr user_set_expr'.data

and encode_user_set_expr (user_set_expr : user_set_expr) : Basic.t =
  match user_set_expr with
  | RoleExpr { data = role', params; _ } ->
    let roleLabel = ("roleLabel", `String role'.data) in
    List.map
      (fun ({ data = name', value'; _ } :
             user_set_param_val' Choreo.named_param')
         ->
        let name = ("name", `String name'.data) in
        match value'.data with
        | Any -> `Assoc [ name ]
        | Expr expr' -> `Assoc [ name; ("value", encode_expr' expr') ])
      params
    |> fun (params : Basic.t list) ->
    `Assoc [ ("roleExpr", `Assoc [ roleLabel; ("params", `List params) ]) ]
  | Initiator event_id' ->
    `Assoc [ ("initiatorExpr", `Assoc [ ("eventId", `String event_id'.data) ]) ]
  | Receiver event_id' ->
    `Assoc [ ("receiverExpr", `Assoc [ ("eventId", `String event_id'.data) ]) ]

and encode_marking ({ is_pending'; is_included'; default_val_opt } : marking) :
    Basic.t =
  let is_pending = ("isPending", `Bool is_pending'.data)
  and is_included = ("isIncluded", `Bool is_included'.data) in
  let (base_marking : (string * Basic.t) list) = [ is_pending; is_included ] in
  Option.fold
    default_val_opt
    ~none:(`Assoc base_marking)
    ~some:(fun (default_val' : value') ->
      `Assoc
        (List.rev
        @@ ("defaultValue", encode_value' default_val')
           :: List.rev base_marking))

and encode_instantiation_constraint' (expr' : expr') : Basic.t =
  encode_instantiation_constraint expr'.data

and encode_instantiation_constraint (expr : expr) : Basic.t =
  `Assoc [ ("instantiationConstraint", encode_expr expr) ]

and encode_ifc_constraint' (expr' : expr') : Basic.t =
  encode_instantiation_constraint expr'.data

and encode_ifc_constraint (expr : expr) : Basic.t =
  `Assoc [ ("ifcConstraint", encode_expr expr) ]

and encode_events (events : event list) : Basic.t list =
  List.map encode_event events
(* |> fun lst -> `Assoc [ ("events", `List lst) ] *)

and encode_event (event : event) : Basic.t =
  let uid = ("endpointElementUID", `String event.uid)
  and element_uid = ("choreoElementUID", `String event.element_uid)
  and id = ("id", `String event.id)
  and label = ("label", `String event.label)
  and data_type =
    ("dataType", encode_type_expr @@ (Option.get !(event.data_expr'.ty)).t_expr)
  and marking = ("marking", encode_marking event.marking) in
  let common =
    ([] : (string * Basic.t) list) |> fun (common : (string * Basic.t) list) ->
    Option.fold event.ifc_constraint_opt ~none:common ~some:(fun x ->
        ("ifcConstraint", encode_expr' x) :: common)
    |> fun (common : (string * Basic.t) list) ->
    Option.fold event.instantiation_constraint_opt ~none:common ~some:(fun x ->
        ("instantiationConstraint", encode_expr' x) :: common)
    |> fun common ->
    uid :: element_uid :: id :: label :: data_type :: marking :: common |> fun common ->
    ("common", `Assoc common)
  in
  match event.data_expr'.data with
  | Input _ -> begin
    match event.communication with
    | Local -> `Assoc [ ("inputEvent", `Assoc [ common ]) ]
    | Tx user_sets ->
      let rcvrs =
        List.map encode_user_set_expr' user_sets |> fun rcvrs ->
        ("receivers", `List rcvrs)
      in
      `Assoc [ ("inputEvent", `Assoc [ common; rcvrs ]) ]
    | Rx user_set ->
      let initrs =
        List.map encode_user_set_expr' user_set |> fun initrs ->
        ("initiators", `List initrs)
      in
      `Assoc [ ("receiveEvent", `Assoc [ common; initrs ]) ]
  end
  | Computation expr' -> (
    let expr = ("dataExpr", encode_expr' expr') in
    match event.communication with
    | Local -> `Assoc [ ("computationEvent", `Assoc [ common; expr ]) ]
    | Tx user_sets ->
      let rcvrs =
        List.map encode_user_set_expr' user_sets |> fun rcvrs ->
        ("receivers", `List rcvrs)
      in
      `Assoc [ ("computationEvent", `Assoc [ common; expr; rcvrs ]) ]
    | Rx user_set ->
      let initrs =
        List.map encode_user_set_expr' user_set |> fun initrs ->
        ("initiators", `List initrs)
      in
      `Assoc [ ("receiveEvent", `Assoc [ common; expr; initrs ]) ])

and encode_relations (relations : relation list) : Basic.t list =
  List.map encode_relation relations
(* |> fun lst ->
  `Assoc [ ("relations", `List lst) ] *)

and encode_relation
    ({ uid
     ; src = src_uid, src_id
     ; instantiation_constraint_opt
     ; relation_type
     ; guard_opt
     } :
      relation) : Basic.t =
  let uid = ("endpointElementUID", `String uid)
  and sourceId = ("sourceId", `String src_uid) in
  let common =
    ([] : (string * Basic.t) list) |> fun (common : (string * Basic.t) list) ->
    Option.fold instantiation_constraint_opt ~none:common ~some:(fun x ->
        ("instantiationConstraint", encode_expr' x) :: common)
    |> fun (common : (string * Basic.t) list) ->
    Option.fold guard_opt ~none:common ~some:(fun x ->
        ("guard", encode_expr' x) :: common)
    |> fun (common : (string * Basic.t) list) ->
    uid :: sourceId :: common |> fun (common : (string * Basic.t) list) ->
    ("relationCommon", `Assoc common)
  in
  match relation_type with
  | ControlFlowRelation { target = target_uid, _; rel_type } ->
    let target = ("targetId", `String target_uid)
    and rel_type =
      begin
        match rel_type with
        | Include -> ("relationType", `String "include")
        | Exclude -> ("relationType", `String "exclude")
        | Response -> ("relationType", `String "response")
        | Condition -> ("relationType", `String "condition")
        | Milestone -> ("relationType", `String "milestone")
      end
    in
    `Assoc [ ("controlFlowRelation", `Assoc [ common; target; rel_type ]) ]
  | SpawnRelation { trigger_id; graph } ->
    let trigger_id = ("triggerId", `String trigger_id) in
    let (graph : string * Basic.t) = ("graph", `Assoc (encode_graph graph)) in
    `Assoc [ ("spawnRelation", `Assoc [ common; trigger_id; graph ]) ]

(* `Assoc [ ("TODO [encode relation]", `String "TODO [encode relation]") ] *)

and encode_role_decl (role_decl : role_decl) : Basic.t =
  let label', param_decls = role_decl in
  let role_label = ("label", `String label'.data)
  and (param_types : Basic.t list) =
    List.map
      (fun ((param_name', param_type') : Choreo.identifier' * Choreo.type_expr')
         ->
        let (name : string * Basic.t) = ("name", `String param_name'.data)
        and (param_type : string * Basic.t) =
          ("type", encode_type_expr' param_type')
        in
        `Assoc [ name; param_type ])
      (Choreo.deannotate_list param_decls)
  in
  `Assoc [ role_label; ("params", `List param_types) ]

and encode_graph ({ events; relations; _ } : endpoint) : (string * Basic.t) list
    =
  let events =
    if List.is_empty events then None else Some (encode_events events)
  and relations =
    if List.is_empty relations then None else Some (encode_relations relations)
  in
  ([] : (string * Basic.t) list) |> fun (graph : (string * Basic.t) list) ->
  Option.fold relations ~none:graph ~some:(fun x ->
      ("relations", `List x) :: graph)
  |> fun (graph : (string * Basic.t) list) ->
  Option.fold events ~none:graph ~some:(fun x -> ("events", `List x) :: graph)

and encode_endpoint_process (endpoint : endpoint) : string * string =
  let role_label = (fst endpoint.role_decl).data in
  let (endpoint : Basic.t) =
    `Assoc
      [ ("role", encode_role_decl endpoint.role_decl)
      ; ("graph", `Assoc (encode_graph endpoint))
      ]
  in
  (role_label, Yojson.Basic.pretty_to_string @@ endpoint)

(* {"p3": "a_string"; "p4": {"p5": {"p1": true; "p2": 3}} } *)
let test_record_val () =
  let open Choreo in
  let field1 = annotate (annotate "p1", annotate (BoolVal true)) in
  let field2 = annotate (annotate "p2", annotate (IntVal 3))
  and field3 = annotate (annotate "p3", annotate (StringVal "a_string")) in
  let record_val = RecordVal [ field1; field2 ] in
  let field4 =
    annotate
      ( annotate "p4"
      , annotate (RecordVal [ annotate (annotate "p5", annotate record_val) ])
      )
  in
  let record_val' = annotate (RecordVal [ field3; field4 ]) in
  print_endline @@ Yojson.Basic.pretty_to_string @@ encode_value' record_val'

let test_markings () =
  let open Choreo in
  let is_pending' = annotate false
  and is_included' = annotate true
  and default_val_opt = Some (annotate (IntVal 3)) in
  let no_value_marking =
    { is_pending'; is_included'; default_val_opt = Option.None }
  and int_valued_marking = { is_pending'; is_included'; default_val_opt } in
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ encode_marking no_value_marking;
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ encode_marking int_valued_marking

let test_type_exprs () =
  let open Choreo in
  let unit_ty = Some { t_expr = UnitTy; is_const = true }
  and bool_ty = Some { t_expr = BoolTy; is_const = true }
  and int_ty = Some { t_expr = IntTy; is_const = true }
  and string_ty = Some { t_expr = StringTy; is_const = true }
  and ref_ty = Some { t_expr = EventRefTy ("E0", true); is_const = true } in

  let plain_int_ty' = annotate ~ty:int_ty IntTy
  and plain_void_ty' = annotate ~ty:unit_ty UnitTy
  and bool_ty_field' = annotate (annotate "p1", annotate ~ty:bool_ty BoolTy)
  and string_ty_field' =
    annotate (annotate "p2", annotate ~ty:string_ty StringTy)
  and ref_ty_field' =
    annotate (annotate "p4", annotate ~ty:ref_ty (EventTy "E1"))
  in
  let rec_ty =
    Some
      { t_expr = RecordTy [ string_ty_field'; bool_ty_field' ]
      ; is_const = true
      }
  in
  let nested_rec_ty_field' =
    annotate
      ( annotate "p3"
      , annotate ~ty:rec_ty (RecordTy [ string_ty_field'; bool_ty_field' ]) )
  in
  let rec_ty = annotate (RecordTy [ ref_ty_field'; nested_rec_ty_field' ]) in
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ encode_type_expr' plain_int_ty';
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ encode_type_expr' plain_void_ty';
  print_endline @@ Yojson.Basic.pretty_to_string @@ encode_type_expr' rec_ty

let test_computations_exprs () =
  let open Choreo in
  let bool_lit_expr' = annotate True
  and event_ref_expr' = annotate @@ EventRef (annotate "E0") in
  let nested_record_expr' =
    annotate
    @@ Record
         [ annotate (annotate "p1", bool_lit_expr')
         ; annotate (annotate "p2", event_ref_expr')
         ]
  in
  let binary_int_add' =
    annotate
    @@ BinaryOp
         ( annotate ~ty:(Some { t_expr = IntTy; is_const = true }) (IntLit 2)
         , annotate ~ty:(Some { t_expr = IntTy; is_const = true }) (IntLit 3)
         , Add )
  in
  let propDeref' =
    annotate
    @@ PropDeref
         ( annotate @@ PropDeref (event_ref_expr', annotate "value")
         , annotate "cid" )
  in
  let record_expr' =
    annotate
    @@ Record
         [ annotate (annotate "p3", bool_lit_expr')
         ; annotate (annotate "p4", nested_record_expr')
         ; annotate (annotate "p5", propDeref')
         ; annotate (annotate "p6", binary_int_add')
         ]
  in
  print_endline @@ Yojson.Basic.pretty_to_string @@ encode_expr' record_expr'

let test_user_set_exprs () =
  let annotate = Choreo.annotate in
  let role_expr_param_p1 = annotate (annotate "p1", annotate Any)
  and role_expr_param_p2 =
    annotate (annotate "p2", annotate (Expr (annotate (Choreo.IntLit 2))))
  in
  let role_expr' =
    annotate
      (RoleExpr
         (annotate (annotate "P", [ role_expr_param_p1; role_expr_param_p2 ])))
  in
  let receiver_expr' = annotate (Receiver (annotate "e0")) in
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ encode_user_set_expr' role_expr';
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ encode_user_set_expr' receiver_expr'

let test_computation_event () =
  let annotate = Choreo.annotate
  and (ty : Choreo.type_info option) =
    Some { t_expr = BoolTy; is_const = true }
  in
  let uid = "e0_0_tx"
  and element_uid = "0"
  and id = "e0"
  and label = "E0"
  and data_expr' =
    let computation = annotate ~ty Choreo.True in
    annotate ~ty (Choreo.Computation computation)
  and (marking : Choreo.event_marking) =
    let is_pending' = annotate false
    and is_included' = annotate true
    and default_val_opt = Some (annotate ~ty (Choreo.BoolVal true)) in
    { is_pending'; is_included'; default_val_opt }
  (* and instantiation_constraint' = annotate ~ty Choreo.True  *)
  and ifc_constraint_opt = Some (annotate ~ty Choreo.True)
  and communication =
    let receivers =
      let role_expr_param_p1 = annotate (annotate "p1", annotate Any)
      and role_expr_param_p2 =
        annotate (annotate "p2", annotate (Expr (annotate (Choreo.IntLit 2))))
      in
      let role_expr' =
        annotate
          (RoleExpr
             (annotate
                (annotate "P", [ role_expr_param_p1; role_expr_param_p2 ])))
      in
      [ role_expr' ]
    in
    Tx receivers
  in
  let endpoint =
    { element_uid
      ;uid
    ; id
    ; label
    ; data_expr'
    ; marking
    ; instantiation_constraint_opt = None
    ; ifc_constraint_opt
    ; communication
    }
  in
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ `List (encode_events [ endpoint ])

let test_input_event () =
  let annotate = Choreo.annotate
  and (ty : Choreo.type_info option) =
    Some { t_expr = BoolTy; is_const = true }
  in
  let uid = "e0_0_tx"
  and element_uid = "0"
  and id = "e0"
  and label = "E0"
  and data_expr' =
    let input = annotate ~ty Choreo.BoolTy in
    annotate ~ty (Choreo.Input input)
  and (marking : Choreo.event_marking) =
    let is_pending' = annotate false
    and is_included' = annotate true
    and default_val_opt = Some (annotate ~ty (Choreo.BoolVal true)) in
    { is_pending'; is_included'; default_val_opt }
  and instantiation_constraint_opt = Some (annotate ~ty Choreo.True)
  and ifc_constraint_opt = Some (annotate ~ty Choreo.True)
  and communication =
    let receivers =
      let role_expr_param_p1 = annotate (annotate "p1", annotate Any)
      and role_expr_param_p2 =
        annotate (annotate "p2", annotate (Expr (annotate (Choreo.IntLit 2))))
      in
      let role_expr' =
        annotate
          (RoleExpr
             (annotate
                (annotate "P", [ role_expr_param_p1; role_expr_param_p2 ])))
      in
      [ role_expr' ]
    in
    Tx receivers
  in
  let endpoint =
    { uid
    ;element_uid
    ; id
    ; label
    ; data_expr'
    ; marking
    ; instantiation_constraint_opt
    ; ifc_constraint_opt
    ; communication
    }
  in

  print_endline @@ Yojson.Basic.pretty_to_string
  @@ `List (encode_events [ endpoint ])

let test_receive_event () =
  let annotate = Choreo.annotate
  and (ty : Choreo.type_info option) =
    Some { t_expr = BoolTy; is_const = true }
  in
  let uid = "e0_0_tx"
  and element_uid = "0"
  and id = "e0"
  and label = "E0"
  and data_expr' =
    let input = annotate ~ty Choreo.BoolTy in
    annotate ~ty (Choreo.Input input)
  and (marking : Choreo.event_marking) =
    let is_pending' = annotate false
    and is_included' = annotate true
    and default_val_opt = Some (annotate ~ty (Choreo.BoolVal true)) in
    { is_pending'; is_included'; default_val_opt }
  and instantiation_constraint_opt = Some (annotate ~ty Choreo.True)
  and ifc_constraint_opt = None
  and communication =
    let initiators =
      let role_expr_param_p1 = annotate (annotate "p1", annotate Any)
      and role_expr_param_p2 =
        annotate (annotate "p2", annotate (Expr (annotate (Choreo.IntLit 2))))
      in
      let role_expr' =
        annotate
          (RoleExpr
             (annotate
                (annotate "P", [ role_expr_param_p1; role_expr_param_p2 ])))
      in
      role_expr'
    in
    Rx [ initiators ]
  in
  let endpoint =
    { uid
    ; element_uid
    ; id
    ; label
    ; data_expr'
    ; marking
    ; instantiation_constraint_opt
    ; ifc_constraint_opt
    ; communication
    }
  in
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ `List (encode_events [ endpoint ])
