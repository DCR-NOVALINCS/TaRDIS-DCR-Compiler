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
(* let json_events =  *)

let test () =
  print_endline @@ Yojson.Basic.pretty_to_string
  @@ encode_event ~uid:"2" ~id:"3"

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
