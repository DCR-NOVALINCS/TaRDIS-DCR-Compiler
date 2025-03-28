module Choreo : module type of Frontend.Syntax

module StringSet : module type of Set.Make (String)

module StringMap : module type of Map.Make (String)

type label_info =
  { ty_info : Choreo.type_info
  ; uid : Choreo.element_uid
  }

type typecheck_result =
  { event_nodes_by_uid : event_node StringMap.t
  ; event_types : label_info StringMap.t
  ; relations : (Choreo.relation' * Choreo.element_uid Utils.Env.t) list
  }

and event_node =
  { event : Choreo.event'
  ; data_dependency : Preprocessing.data_dependency option
  ; uid_env : Choreo.element_uid Utils.Env.t
  ; userset_alias_types : Choreo.type_info StringMap.t
  }

val check_program :
     Preprocessing.preprocessing_result
  -> (typecheck_result, (Frontend.Syntax.loc * string) list) result
