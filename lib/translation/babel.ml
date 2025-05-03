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

and encode_type_expr' (type_expr' : Choreo.type_expr') : string * Basic.t =
  encode_type_expr type_expr'.data

and encode_type_expr (type_expr : Choreo.type_expr) : string * Basic.t =
  match type_expr with
  | Choreo.UnitTy -> ("valueType", `String "void")
  | Choreo.BoolTy -> ("valueType", `String "bool")
  | Choreo.IntTy -> ("valueType", `String "int")
  | Choreo.StringTy -> ("valueType", `String "string")
  | Choreo.EventRefTy (label, _) | Choreo.EventTy label ->
    ("eventType", `Assoc [ ("label", `String label) ])
  | Choreo.RecordTy ty_fields ->
    List.fold_left
      (fun (assoc_list : Basic.t list)
           ((name', type_expr') : Choreo.identifier' * Choreo.type_expr')
         ->
        `Assoc
          [ ("name", `String name'.data)
          ; ("type", `Assoc [ encode_type_expr type_expr'.data ])
          ]
        :: assoc_list)
      []
      (Choreo.deannotate_list ty_fields)
    |> fun (type_fields : Basic.t list) ->
    ("recordType", `Assoc [ ("fields", `List type_fields) ])
  | _ -> assert false

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

and encode_user_set_expr' (user_set_expr' : user_set_expr') =
  encode_user_set_expr user_set_expr'.data

and encode_user_set_expr (user_set_expr : user_set_expr) =
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
      `Assoc [ ("initiatorExpr", `Assoc [("eventId",`String event_id'.data)]) ]
    | Receiver event_id' -> `Assoc [ ("receiverExpr", `Assoc [("eventId",`String event_id'.data)]) ]
  

let encode_data_expr (data_expr : Choreo.data_expr) : Basic.t =
  match data_expr with
  | Choreo.Input type_expr' ->
    `Assoc [ ("type_expr", `Assoc [ encode_type_expr type_expr'.data ]) ]
  | Choreo.Computation _expr' -> assert false

let encode_event ~(uid : string) ~(id : string) : Basic.t =
  `Assoc [ ("uid", `String uid); ("id", `String id) ]

let encode_events (events : event list) : Basic.t =
  List.fold_left
    (fun (acc : Basic.t list) event ->
      let uid = ("uid", `String event.uid)
      and id = ("id", `String event.id)
      and data_expr = ("data_expr", encode_data_expr event.data_expr) in
      `Assoc [ uid; id; data_expr ] :: acc)
    []
    events
  |> fun lst -> `Assoc [ ("events", `List lst) ]

let encode_endpoint_process (endpoint_process : endpoint) =
  let { events; relations } = endpoint_process in
  print_endline @@ Yojson.Basic.pretty_to_string @@ encode_events events

let encode_marking ({ is_pending'; is_included'; default_val_opt } : marking) :
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
  let plain_int_ty' = annotate IntTy
  and plain_void_ty' = annotate UnitTy
  and string_ty_field' = annotate (annotate "p1", annotate StringTy)
  and bool_ty_field' = annotate (annotate "p2", annotate BoolTy) in
  let nested_rec_ty_field' =
    annotate
      (annotate "p3", annotate (RecordTy [ string_ty_field'; bool_ty_field' ]))
  in
  let plain_ref_ty' = annotate (annotate "pp4", annotate (EventTy "E0")) in
  let rec_ty = annotate (RecordTy [ plain_ref_ty'; nested_rec_ty_field' ]) in
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ `Assoc [ encode_type_expr' plain_int_ty' ];
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ `Assoc [ encode_type_expr' plain_void_ty' ];
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ `Assoc [ encode_type_expr' rec_ty ]

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
  print_endline @@ Yojson.Basic.pretty_to_string @@ encode_user_set_expr' role_expr';
  print_endline @@ Yojson.Basic.pretty_to_string @@ encode_user_set_expr' receiver_expr'
