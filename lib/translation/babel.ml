(* module Choreo = Tardis.Syntax.Choreo *)
open Endpoint_projection.Endpoint
open Yojson

let rec encode_type_expr (type_expr : Choreo.type_expr) : string * Basic.t =
  match type_expr with
  | Choreo.UnitTy -> ("unit", `String "")
  | Choreo.BoolTy -> ("primitive", `String "bool")
  | Choreo.IntTy -> ("primitive", `String "int")
  | Choreo.StringTy -> ("primitive", `String "str")
  | Choreo.EventRefTy (event_id, _) | Choreo.EventTy event_id ->
    ("event_ref", `String event_id)
  | Choreo.RecordTy ty_fields ->
    List.fold_left
      (fun assoc_list
           ((name', type_expr') : Choreo.identifier' * Choreo.type_expr')
         ->
        (name'.data, `Assoc [ encode_type_expr type_expr'.data ]) :: assoc_list)
      []
      (Choreo.deannotate_list ty_fields)
    |> List.fold_left (fun acc (name, ty_field) -> (name, ty_field) :: acc) []
    |> fun record_ty_fields ->
    let t : string * Basic.t = ("record", `Assoc record_ty_fields) in
    t
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

let rec encode_value (value' : value') =
  match value'.data with
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
        and field_value = ("value", encode_value value') in
        `Assoc [ field_name; field_value ] :: acc)
      []
      fields
    |> fun lst ->
    `Assoc [ ("fields", `List (List.rev lst)) ] |> fun rec_val ->
    `Assoc [ ("recordVal", rec_val) ]

(* let encode_marking (marking : marking) =
  let value = *)

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
  let record_val = annotate (RecordVal [ field3; field4 ]) in
  print_endline @@ Yojson.Basic.pretty_to_string @@ encode_value record_val

(* 
  
  "type_expr" : {"type" : "String"}
  {
  "type" : {"primitive" : "String"}

  "type" : {
    "record": [
      { "a" : {"primitive" : "String"},
      { "b" :
        {"record" : [
            {primitive : "Integer"}
          ]
        }
    ]
  }

  }
  
  
  *)
