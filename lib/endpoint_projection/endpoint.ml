module Choreo = Frontend.Syntax  
open Userset_encoding
 
type endpoint  = {
  events: event list
  ; relations : relation list
}

(**
[uid] unique id assigned to every event
*)
and event =
  { uid : Choreo.identifier
  ; id : Choreo.event_id
  ; label : Choreo.event_ty
  ; data_expr : Choreo.data_expr
  ; marking : marking
  ; self : CnfRole.t
  ; communication : communication
  ; symbols : Choreo.expr' StringMap.t
  }

  and marking = Choreo.event_marking



(*
    =============================================================================
    Values, Computation Expressions and Type Epxressions
    =============================================================================
  *)

  and record_field_val' = Choreo.value' Choreo.named_param'
  
  and value' = Choreo.value'

  and relation =
    | ControlFlowRelation of
        Choreo.element_uid
        * (Choreo.element_uid * Choreo.event_id)
        * (Choreo.element_uid * Choreo.event_id)
        * Choreo.relation_type
        * CnfRole.t
    | SpawnRelation of Choreo.element_uid * (Choreo.element_uid * Choreo.event_id) * endpoint

  and communication =
    | Local
    | Tx of CnfUserset.t
    | Rx of CnfUserset.t

  and param_value =
    | BoolLit of bool
    | IntLit of int
    | StringLit of string
    | Symbolic of Choreo.identifier

    let rec unparse_events ?(indent = "") (events : event list) =
      let rec unparse_event (e : event) =
        (* TODO move next indent somewhere else later on - proper unparser *)
        let next_indent = indent ^ "  " in
        let rec unparse_info () =
          Printf.sprintf "(%s : %s)" e.id e.label
        and unparse_participants roles =
          StringMap.bindings roles
          |> List.map (fun (_, constrained_role) ->
                 CnfRole.to_string constrained_role)
          |> String.concat ", "
        and unparse_communication = function
          | Local ->
            Printf.sprintf "[Local]\n%s%s" next_indent (CnfRole.to_string e.self)
          | Tx receivers ->
            Printf.sprintf
              "[Tx]\n%s%s\n%s%s->  %s"
              next_indent
              (CnfRole.to_string e.self)
              next_indent
              next_indent
              (unparse_participants receivers)
          | Rx initiators ->
            Printf.sprintf
              "[Rx]\n%s%s\n%s%s->  %s"
              next_indent
              (unparse_participants initiators)
              next_indent
              next_indent
              (CnfRole.to_string e.self)
        and unparse_symbols () =
          List.map
            (fun (sym, expr') ->
              Printf.sprintf "%s:%s" sym (Frontend.Unparser.unparse_expr expr'))
            (StringMap.bindings e.symbols)
          |> String.concat ", " |> Printf.sprintf "(%s)"
        in
        Printf.sprintf
          "%s(uid:%s)  %s %s  %s"
          indent
          e.uid 
          (unparse_info ())
          (unparse_symbols ())
          (unparse_communication e.communication)
      in
      List.map unparse_event events |> String.concat "\n\n"
  
    and unparse_relation ?(indent = "") = function
      | ControlFlowRelation
          (_uid, (src_uid, src_id), (target_uid, target_id), rel_type, self) ->
        Printf.sprintf
          "%s(%s,%s) %s (%s,%s) %s"
          indent
          src_uid
          src_id
          (Frontend.Unparser.unparse_ctrl_flow_relation_type rel_type)
          target_uid
          target_id
          (CnfRole.to_string self)
      | SpawnRelation (_uid, (src_uid, src_id), projection) ->
        let unparsed_projection =
          unparse_projection ~indent:(indent ^ "  ") projection
        in
        Printf.sprintf
          "%s(%s, %s) -->> {\n%s\n%s}"
          indent
          src_uid
          src_id
          unparsed_projection
          indent
  
    and unparse_relations ?(indent = "") (relations : relation list) =
      List.map (unparse_relation ~indent) relations |> String.concat "\n"
    (* |> String.cat (indent ^ "\n;\n") *)
  
    and unparse_projection ?(indent = "") ({ events; relations } : endpoint) =
      let unparsed_events = unparse_events ~indent events
      and unparsed_relations = unparse_relations ~indent relations in
      if unparsed_relations = "" then unparsed_events
      else
        Printf.sprintf "%s\n%s;\n\n%s" unparsed_events indent unparsed_relations
