open Endpoint_projection.Endpoint
open Yojson


let rec encode_value' (value' : value') =
  encode_value value'.data
  
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

let encode_data_expr (data_expr : Choreo.data_expr) : Basic.t =
  match data_expr with
  | Choreo.Input type_expr' ->
    `Assoc [ ("type_expr", `Assoc [ encode_type_expr type_expr'.data ]) ]
  | Choreo.Computation expr' -> assert false

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
        @@ (("defaultValue", encode_value' default_val') :: List.rev base_marking)
        ))

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

  
