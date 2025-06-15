module Choreo = Frontend.Syntax
open Userset_encoding

type endpoint =
  { role_decl : role_decl
  ; events : event list
  ; relations : relation list
  }

(** [uid] globally unique id

    [id] locally unique id

    [label] event label (communicates event's type)

    [data_expr] input/computation

    [marking] marking

    [instantiation_constraint] computation exmpression *)
and event =
  { uid : Choreo.identifier
  ; element_uid : Choreo.element_uid
  ; id : Choreo.event_id
  ; label : Choreo.event_ty
  ; data_expr' : Choreo.data_expr'
  ; marking : marking
  ; instantiation_constraint_opt : expr' option
  ; ifc_constraint_opt : expr' option
  ; communication : communication
  }

and marking = Choreo.event_marking

and role_decl = Choreo.value_dep_role_decl

and identifier' = Choreo.identifier'

(*
    =============================================================================
    Values, Computation Expressions and Type Epxressions
    =============================================================================
*)
and record_field_val' = Choreo.value' Choreo.named_param'

and value' = Choreo.value'

and value = Choreo.value

and record_field_expr' = Choreo.expr' Choreo.named_param'

and expr' = Choreo.expr'

and expr = Choreo.expr

(*
    =============================================================================
    User-Set Expressions
    =============================================================================
*)
and user_set_param_val' = user_set_param_val Choreo.annotated

and user_set_param_val =
  | Expr of expr'
  | Any

and userset_role_expr' = user_set_param_val' Choreo.parameterisable_role'

and user_set_expr' = user_set_expr Choreo.annotated

and user_set_expr =
  | RoleExpr of userset_role_expr'
  | Initiator of Choreo.event_id'
  | Receiver of Choreo.event_id'

and relation =
  { uid : Choreo.element_uid
  ; src : Choreo.element_uid * Choreo.event_id
  ; guard_opt : expr' option
  ; relation_type : relation_t
  ; instantiation_constraint_opt : expr' option
  }

and relation_t =
  | ControlFlowRelation of
      { target : Choreo.element_uid * Choreo.event_id
      ; rel_type : Choreo.relation_type
      }
  | SpawnRelation of
      { trigger_id : Choreo.identifier
      ; graph : endpoint
      }

and communication =
  | Local
  | Tx of user_set_expr' list
  | Rx of user_set_expr' list

and param_value =
  | BoolLit of bool
  | IntLit of int
  | StringLit of string
  | Symbolic of Choreo.identifier