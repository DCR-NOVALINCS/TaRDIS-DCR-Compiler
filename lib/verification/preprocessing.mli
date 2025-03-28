module Choreo : module type of Frontend.Syntax 

module StringSet : module type of Set.Make (String)

module StringMap : module type of Map.Make (String)

type data_dependency =
  | ValueDependency of StringSet.t
  | TypeDependency of StringSet.t

and event_node =
  { event : Choreo.event'
  ; uid_env : Choreo.element_uid Utils.Env.t
  ; data_dependency : data_dependency option
  ; userset_alias_types : Choreo.type_info StringMap.t
  }

and preprocessing_result =
  { value_dep_roles :
      (Choreo.identifier' * Choreo.type_expr' Choreo.named_param' StringMap.t)
      StringMap.t
  ; event_nodes_by_uid : event_node StringMap.t
  ; event_types : StringSet.t
  ; relations : (Choreo.relation' * Choreo.element_uid Utils.Env.t) list
  }

val preprocess_program :
  Choreo.program -> (preprocessing_result, (Choreo.loc * string) list) result
