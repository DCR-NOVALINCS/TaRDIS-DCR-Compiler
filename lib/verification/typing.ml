module StringMap = Map.Make (String)
module StringSet = Set.Make (String)
module Choreo = Frontend.Syntax
module Env = Utils.Env
open Choreo
open Utils.Results

(* information associated with every event label in the program (set during typecheck)
    - type_expr: type of the event's data expression
    - uid: the event which first declared the type_expr
*)
type label_info =
  { ty_info : type_info
  ; uid : element_uid
  }

(* information collected/required during typecheck:
    - typecheck_graph: program events and their typecheck dependencies (available after preprocessing);
    - event_types: program labels (initialized during preprocessing, updated during typechecking);
    - relations: keeps relations and respective env closures for id -> uid mapping;
*)
(* TODO [revisit event_types] requires post-refactoring adjustments
  (option ref StringMap.t is not great...) *)
and typechecheck_context =
  { value_dep_roles :
      (identifier' * type_expr' named_param' StringMap.t) StringMap.t
  ; typecheck_graph : (element_uid * typecheck_node) list
  ; event_types : label_info option ref StringMap.t
  ; relations : (relation' * element_uid Env.t) list
  }

(** A node in the "typecheck graph":
    - event: the event itself;
    - type_dependencies: the labels whose type must known prior to typechecking
      the event;
    - event_dependencies: the events whose type must be known prior to
      typechecking the event;
    - uid_env: the uid environment visible to the event (for typechecking
      purposes); *)
and typecheck_node =
  { event' : event'
  ; data_dependency : Preprocessing.data_dependency option
  ; uid_env : element_uid Env.t
  ; userset_alias_types : type_info StringMap.t
  }

and typecheck_result =
  { event_nodes_by_uid : event_node StringMap.t
  ; event_types : label_info StringMap.t
  ; relations : (relation' * element_uid Env.t) list
  }

(* TODO [revisit] data_dependency would benefit from a finer granularity (@trigger vs 
direct event access) *)
and event_node =
  { event : event'
  ; data_dependency : Preprocessing.data_dependency option
  ; uid_env : element_uid Env.t
  ; userset_alias_types : type_info StringMap.t
  }

let to_string_map :
    'a.
       'a annotated named_param' list
    -> ('a annotated named_param' -> string)
    -> ('a annotated named_param' StringMap.t, _) result =
 fun entries on_err_duplicate_fields ->
  let add_one map entry' =
    let k', v' = entry'.data in
    match StringMap.find_opt k'.data map with
    | None -> Ok (StringMap.add k'.data entry' map)
    | Some prev_decl -> Error [ (v'.loc, on_err_duplicate_fields prev_decl) ]
  in
  fold_left_error add_one StringMap.empty entries

let assert_same_keys (map1 : 'a named_param' StringMap.t)
    (map2 : 'b named_param' StringMap.t) error_msg =
  let merger _key opt1 opt2 =
    match (opt1, opt2) with
    | None, Some v -> Some v
    | _, _ -> None
  in
  match StringMap.choose_opt StringMap.(merge merger map1 map2) with
  | None -> Ok ()
  | Some (_, entry) -> Error [ (entry.loc, error_msg entry) ]

(* =========================================================================
   ==================== DEBUG section (temporary: to remove) =============== *)

let debug_relations relations =
  let open Frontend.Unparser in
  List.iter
    (fun (rel, _) ->
      print_endline @@ "(" ^ string_of_loc rel.loc ^ ")\n"
      ^ unparse_relations "" true [ rel ])
    relations

let debug_event_types event_types =
  let open Frontend.Unparser in
  let event_ty_to_string entry =
    begin
      match !entry with
      | None -> "Undefined"
      | Some { ty_info = { t_expr; is_const }; uid } ->
        let ty_string = unparse_type t_expr in
        Printf.sprintf "ty= <%s, %b> ; uid: [%s]" ty_string is_const uid
    end
  in

  let event_info_to_string (key, value) =
    Printf.sprintf "%s -> %s" key (event_ty_to_string value)
  in

  let event_info_string_list = List.map event_info_to_string event_types in
  print_endline "\n===== DEBUG event types ==\n=";
  print_endline @@ String.concat "\n" event_info_string_list;
  print_endline "=\n===== End event types ==\n\n"

let debug_global_events global_events =
  let global_event_entry_to_string (uid, event) =
    Printf.sprintf "(uid: %s, id: %s)" uid (fst event.data.info.data).data
  in
  let entries = List.map global_event_entry_to_string !global_events in
  print_endline "\n== DEBUG global events ==";
  print_endline @@ String.concat "\n" entries

let debug_preprocessed_events preprocessed_events =
  let open Frontend.Unparser in
  let preprocessed_event_to_string
      ( uid
      , { event' = ev
        ; data_dependency =
            data_dep_opt
            (* ; type_dependencies = deps'
               ; event_dependencies = deps'' *)
        ; _
        } ) =
    let id, _ = ev.data.info.data in
    let data_expr_kind =
      begin
        match ev.data.data_expr.data with
        | Input _ -> "? : "
        | Computation _ -> ""
      end
    in
    let deps =
      match data_dep_opt with
      | Some (ValueDependency set) | Some (TypeDependency set) ->
        StringSet.to_list set
      | None -> []
    in
    Printf.sprintf
      "[%s] uid: %s  id: %s  deps: [%s] ->  type: <%s%s, %b>"
      (Option.get !(ev.uid))
      uid
      id.data
      (String.concat ", " deps)
      data_expr_kind
      (if Option.is_none !(ev.ty) then ""
       else unparse_type @@ (Option.get !(ev.ty)).t_expr)
      (if Option.is_none !(ev.ty) then true else (Option.get !(ev.ty)).is_const)
  in

  let elems = List.map preprocessed_event_to_string preprocessed_events in
  print_endline "\n====== [start] DEBUG events ==\n==";
  print_endline @@ String.concat "\n" elems;
  print_endline "==\n====== [end] DEBUG events =="

(* =========================================================================
   ========================== END of DEBUG section ========================= *)

(** {i (tail recursive)} [equal_types type_1 type_2] indicates whether type
    expressions [type_1] and [type_2] are structurally equal .

    Returns {b true} if the [type_1] and [type_2] are structurally equal, and
    {b false} otherwise. *)
let rec equal_types ty1 ty2 =
  let rec equal_types_aux = function
    | [] -> true
    | (ty1, ty2) :: rest -> (
      match (ty1, ty2) with
      | UnitTy, UnitTy | BoolTy, BoolTy | IntTy, IntTy | StringTy, StringTy ->
        (equal_types_aux [@tailcall]) rest
      | EventTy label1, EventTy label2 ->
        String.equal label1 label2 && (equal_types_aux [@tailcall]) rest
      | EventRefTy (label1, _), EventRefTy (label2, _) ->
        String.equal label1 label2 && (equal_types_aux [@tailcall]) rest
      | RecordTy fields1, RecordTy fields2 ->
        List.compare_lengths fields1 fields2 = 0
        &&
        let compare_by_name { data = name1, _; _ } { data = name2, _; _ } =
          String.compare name1.data name2.data
        in
        let sorted1 = List.sort compare_by_name fields1
        and sorted2 = List.sort compare_by_name fields2 in
        let combined = List.combine sorted1 sorted2 in
        List.for_all (fun (f1, f2) -> compare_by_name f1 f2 = 0) combined
        &&
        let type_pairs =
          List.map
            (fun ({ data = _, v1; _ }, { data = _, v2; _ }) ->
              (v1.data, v2.data))
            combined
        in
        (equal_types_aux [@tailcall]) @@ type_pairs @ rest
      | ListTyEmpty, ListTyEmpty -> true
      | ListTy elem_type_1, ListTy elem_type_2 ->
        (equal_types_aux [@tailcall]) @@ ((elem_type_1, elem_type_2) :: rest)
      | _ -> false)
  in
  equal_types_aux [ (ty1, ty2) ]

and update_type_context ctxt (label' : event_label') (ty_info : type_info)
    (uid : element_uid) =
  let event_types = ctxt.event_types in
  let label_info = StringMap.find label'.data event_types in
  match !label_info with
  | None ->
    label_info := Some { ty_info; uid };
    Ok { ctxt with event_types }
  | Some { ty_info = { t_expr; is_const }; _ } ->
    if
      (equal_types [@taicall]) t_expr ty_info.t_expr
      && is_const = ty_info.is_const
    then Ok ctxt
    else
      Error
        [ ( label'.loc
          , on_err_equally_labelled_events_declare_different_types
              label'
              ty_info.t_expr
              t_expr )
        ]

(** Check whether the node's dependencies are satisfied *)
and can_typecheck ~ctxt:{ typecheck_graph; event_types; _ } node =
  let is_pending_event_dep uid =
    let node = List.assoc uid typecheck_graph in
    Option.is_none !(node.event'.ty)
  and is_pending_ty_dep event_ty =
    let ty = !(StringMap.find event_ty event_types) in
    Option.is_none ty
  in
  (* TODO better bridge the old syntax and the new *)
  let ty_deps, ev_deps =
    match node.data_dependency with
    | Some (ValueDependency set) -> ([], StringSet.to_list set)
    | Some (TypeDependency set) -> (StringSet.to_list set, [])
    | None -> ([], [])
  in
  Option.is_none (List.find_opt is_pending_ty_dep ty_deps)
  && Option.is_none (List.find_opt is_pending_event_dep ev_deps)

and typecheck_events (ctxt : typechecheck_context) =
  let typecheck_event (ctxt, postponed, typechecked) (uid, node) =
    let on_typecheck_res = function
      | Error _ as error -> error
      | Ok ty -> (
        let label = snd node.event'.data.info.data in
        match update_type_context ctxt label ty uid with
        | Ok ctxt ->
          node.event'.ty := Some ty;
          node.event'.data.data_expr.ty := Some ty;
          Ok ctxt
        | Error err -> Error err)
      (* TODO error messages *)
    in
    if can_typecheck ~ctxt node then
      let typecheck_res =
        match node.event'.data.data_expr.data with
        | Input type_expr ->
          on_typecheck_res (Ok { t_expr = type_expr.data; is_const = false })
        | Computation expr ->
          on_typecheck_res (typecheck_expr expr node.uid_env ctxt)
      in
      begin
        match typecheck_res with
        | Ok ctxt -> Ok (ctxt, postponed, true)
        | Error err -> Error err
      end
    else Ok (ctxt, (uid, node) :: postponed, typechecked)
  in
  let rec typecheck_helper ctxt nodes =
    let typecheck_run_result =
      fold_left_error typecheck_event (ctxt, [], false) nodes
    in
    begin
      match typecheck_run_result with
      | Error err -> Error err
      | Ok (ctxt, postponed, made_progress) ->
        if not made_progress then
          Error [ (Nowhere, "Cyclic dependency detected") ]
        else if List.is_empty postponed then Ok ctxt
        else typecheck_helper ctxt @@ List.rev postponed
    end
  in
  typecheck_helper ctxt ctxt.typecheck_graph

(** [typecheck_participant_exprs ctxt] typechecks every event's participants and
    its conformance to the roles declared in the preamble.

    Participants are described via user-set expressions, which it turn are based
    on role-based expressions.

    This function assumes participants have been preprocessed, and that every
    event's data expression has typechecked. Typechecking a participant
    expression amounts to ensuring that every role-based parameter's expression
    conforms to the declared type for that parameter, acording to the roles
    declared in the program's preamble.

    Returns [Ok context], encapsulating the current [context] after a
    successfull validation, or an [Error err ] describing the issue. *)
and typecheck_participant_exprs (ctxt : typechecheck_context) =
  (*
    == typecheck a single parameter instance against the role's declared params
  *)
  let typecheck_user_set_role_expr_param
      ((param_aliases, uid_env, declared_params) :
        type_info StringMap.t
        * element_uid Env.t
        * type_expr' named_param' StringMap.t)
      (param_instance' : user_set_param_val' named_param') =
    let param_name', param_val_expr' = param_instance'.data in
    let _, declared_param_type' =
      (StringMap.find param_name'.data declared_params).data
    in
    match param_val_expr'.data with
    | Expr expr' -> begin
      match expr'.data with
      | EventRef id' ->
        (* reminder: user-set param values cannot be plain event refs - this
           is a binding - we need only to check conformance and set ref *)
        (* TODO check if id'=binding is in scope and output err-msg
           otherwise *)
        let binding_ty = StringMap.find id'.data param_aliases in
        if equal_types binding_ty.t_expr declared_param_type'.data then (
          param_val_expr'.ty := Some binding_ty;
          param_instance'.ty := Some binding_ty;
          Ok (param_aliases, uid_env, declared_params))
        else
          Error
            [ ( param_instance'.loc
              , "user-set param val type: binding and declared do not match" )
            ]
      | _ -> begin
        match typecheck_expr expr' uid_env ctxt with
        | Ok ty_info ->
          if equal_types ty_info.t_expr declared_param_type'.data then (
            param_val_expr'.ty := Some ty_info;
            param_instance'.ty := Some ty_info;
            Ok (param_aliases, uid_env, declared_params))
          else
            Error
              [ ( param_instance'.loc
                , "user-set param val type: actual and declared do not match" )
              ]
        | Error _ as err -> err
      end
    end
    | Any | RuntimeValue _ ->
      let ty_info = { t_expr = declared_param_type'.data; is_const = false } in
      param_val_expr'.ty := Some ty_info;
      param_instance'.ty := Some ty_info;
      Ok (param_aliases, uid_env, declared_params)
    | Alias alias' ->
      let mapped_ty_info = StringMap.find alias'.data param_aliases in
      if equal_types mapped_ty_info.t_expr declared_param_type'.data then (
        param_val_expr'.ty := Some mapped_ty_info;
        param_instance'.ty := Some mapped_ty_info;
        Ok (param_aliases, uid_env, declared_params))
      else Error [ (alias'.loc, "Illegal type - alias param type") ]
  in
  (*
    == typecheck a single user-set expr
  *)
  let typecheck_user_set_expr
      ((ctxt, uid_env, param_aliases) :
        typechecheck_context * element_uid Env.t * type_info StringMap.t)
      (user_set_expr' : user_set_expr') =
    match user_set_expr'.data with
    (* user_set_param_val' parameterisable_role' *)
    | RoleExpr role_expr' -> (
      let role', actual_params = role_expr'.data in
      let _, declared_params = StringMap.find role'.data ctxt.value_dep_roles in
      match
        fold_left_error
          typecheck_user_set_role_expr_param
          (param_aliases, uid_env, declared_params)
          actual_params
      with
      | Ok _ -> Ok (ctxt, uid_env, param_aliases)
      | Error stack_trace ->
        Error
          (( role_expr'.loc
           , "Role instance does not conform with it's declaration" )
          :: stack_trace))
    | Initiator _ | Receiver _ -> Ok (ctxt, uid_env, param_aliases)
  in
  (*
    == typechecks all user-set exprs in a single event
  *)
  let typecheck_event_participants (ctxt : typechecheck_context) (uid, node) =
    (* TODO cleanup *)
    let param_aliases = node.userset_alias_types in
    let uid_env = node.uid_env in
    match node.event'.data.participants.data with
    | Local initiator' ->
      typecheck_user_set_expr (ctxt, uid_env, param_aliases) initiator'
      >>= fun (ctxt, _, _) -> Ok ctxt
    | Interaction (inititator', receivers) ->
      fold_left_error
        typecheck_user_set_expr
        (ctxt, uid_env, param_aliases)
        (inititator' :: receivers)
      >>= fun (ctxt, _, _) -> Ok ctxt
  in
  (*
    == typecheck user-set expressions of all event nodes
  *)
  fold_left_error typecheck_event_participants ctxt ctxt.typecheck_graph


and typecheck_security_levels (ctxt : typechecheck_context) =
  let typecheck_sec_label_param (uid_env, declared_params)
      (param_instance' : sec_label_param' named_param') =
    let param_name', param_val_expr' = param_instance'.data in
    let _, declared_param_type' =
      (StringMap.find param_name'.data declared_params).data
    in
    match param_val_expr'.data with
    | Parameterised expr' -> begin
      match typecheck_expr expr' uid_env ctxt with
      | Ok ty_info ->
        if equal_types ty_info.t_expr declared_param_type'.data then (
          param_val_expr'.ty := Some ty_info;
          param_instance'.ty := Some ty_info;
          Ok (uid_env, declared_params))
        else
          Error
            [ ( param_instance'.loc
              , "Security-label parameter type mismatch: actual and \
                 declared do not match" )
            ]
      | Error _ as err -> err
    end
    | _ -> Ok (uid_env, declared_params)
  in
  let typecheck_security_label
      ((ctxt, uid_env) : typechecheck_context * element_uid Env.t)
      (sec_label' : sec_label') =
      begin
    match sec_label'.data with
    | Sec e -> 
    let role', actual_params = e.data in
    let _, declared_params = StringMap.find role'.data ctxt.value_dep_roles in
    begin match
      fold_left_error
        typecheck_sec_label_param
        (uid_env, declared_params)
        actual_params
    with
    | Ok _ -> Ok (ctxt, uid_env)
    | Error stack_trace ->
      Error
        (( role'.loc
         , "TODO err-msg-fun: role instance does not conform with it's \
            declaration" )
        :: stack_trace)
    end
    | SecExpr expr' ->
      begin match typecheck_expr expr' uid_env ctxt with
      | Ok ty_info ->
        sec_label'.ty := Some ty_info;
        Ok (ctxt, uid_env)
      | Error _ as err -> err
      end
    end
  in

  let typecheck_security_level (ctxt : typechecheck_context) (uid, node) =
    let security_labels = node.event'.data.security_level.data in
    let uid_env = node.uid_env in
    fold_left_error typecheck_security_label (ctxt, uid_env) security_labels
    >>= fun (ctxt, _) -> Ok ctxt
  in

  fold_left_error typecheck_security_level ctxt ctxt.typecheck_graph

and typecheck_relations ctxt =
  let typecheck_relation ctxt (relation, env) =
    let extract_guard = function
      | ControlRelation (_, guard, _, _) | SpawnRelation (_, _, guard, _) ->
        guard
    and validate_typecheck_res = function
      | Error err -> Error ((relation.loc, bad_expr_in_relation_guard) :: err)
      | Ok { t_expr = BoolTy; _ } -> Ok ctxt
      | Ok ty -> Error [ (relation.loc, non_boolean_expr_in_relation_guard ty) ]
    in
    typecheck_expr (extract_guard relation.data) env ctxt
    |> validate_typecheck_res
  in
  fold_left_error typecheck_relation ctxt ctxt.relations

and non_boolean_expr_in_relation_guard curr_type =
  let open Frontend.Unparser in
  Printf.sprintf
    "Illegal expression in relation guard; guard expression must evaluate to a \
     boolean: found %s"
  @@ unparse_type curr_type.t_expr

and bad_expr_in_relation_guard = "Bad expression in relation guard."

and typecheck_expr ?(force_const = false) (expr' : expr')
    (env : element_uid Env.t) ctxt :
    (type_info, (loc * element_uid) list) result =
  let get_event_node_by_id (id' : event_id') =
    (* follow pointer to get event *)
    let uuid = Option.get @@ Env.find_flat_opt id'.data env in
    let event_node = List.assoc uuid ctxt.typecheck_graph in
    event_node
  in
  (* ancillary: sets type_info for global expr being typechecked *)
  let set_ty_info ?(force_const = false) (t_expr, is_const) =
    let ty_info = { t_expr; is_const = is_const || force_const } in
    expr'.ty := Some ty_info;
    Ok ty_info
  in
  (* ancillary: typechecks an event-ref expr *)
  let typecheck_event_ref_helper ?(force_const = false) event_id =
    (* fetch actual event *)
    let uid = Option.get @@ Env.find_flat_opt event_id env in
    let typecheck_node = List.assoc uid ctxt.typecheck_graph in
    (* retrieve its label/EventTy and 'const' state *)
    let _, label = typecheck_node.event'.data.info.data
    and { is_const; _ } =
      Option.get !(typecheck_node.event'.data.data_expr.ty)
    in
    set_ty_info (EventRefTy (label.data, is_const || force_const), true)
  in

  let typecheck_record_field_helper ?(force_const = false)
      (field : record_field') (acc : record_field_ty' list * bool) =
    let name', value' = field.data in
    match typecheck_expr ~force_const value' env ctxt with
    | Error _ as err -> err
    | Ok ({ t_expr; is_const } as ty_info) ->
      (* obs: currently also annotating the field(name:value) with the same type as in
         "the type of the field, reflects the type of its value" *)
      field.ty := Some ty_info;
      let type_expr = annotate ~loc:value'.loc ~ty:(Some ty_info) t_expr in
      let record_field_ty = annotate ~loc:field.loc (name', type_expr) in
      let field_types, all_const = acc in
      Ok (record_field_ty :: field_types, all_const && (is_const || force_const))
  in

  match expr'.data with
  | True | False -> set_ty_info (BoolTy, true)
  | IntLit _ -> set_ty_info (IntTy, true)
  | StringLit _ -> set_ty_info (StringTy, true)
  | Parenthesized enclosed_expr -> begin
    match typecheck_expr ~force_const enclosed_expr env ctxt with
    | Error _ as err -> err
    | Ok { t_expr; is_const } -> set_ty_info ~force_const (t_expr, is_const)
  end
  | BinaryOp (e1, e2, op) -> (
    let ty_info1 = typecheck_expr ~force_const e1 env ctxt in
    if Result.is_error ty_info1 then ty_info1
    else
      let ty_info2 = typecheck_expr ~force_const e2 env ctxt in
      if Result.is_error ty_info2 then ty_info2
      else
        match (ty_info1, ty_info2) with
        | ( Ok { t_expr = IntTy; is_const = is_const1 }
          , Ok { t_expr = IntTy; is_const = is_const2 } ) -> begin
          let is_const = is_const1 && is_const2 in
          match op with
          | Add | Mult -> set_ty_info (IntTy, is_const)
          | GreaterThan | LessThan | Eq | NotEq -> set_ty_info (BoolTy, is_const)
          | _ ->
            Error
              [ (expr'.loc, "TODO unexpected operator for Integer arguments") ]
        end
        | ( Ok { t_expr = BoolTy; is_const = is_const1 }
          , Ok { t_expr = BoolTy; is_const = is_const2 } ) -> begin
          let is_const = is_const1 && is_const2 in
          match op with
          | And | Or | Eq | NotEq -> set_ty_info (BoolTy, is_const)
          | _ ->
            Error
              [ (expr'.loc, "TODO unexpected operator for Boolean arguments") ]
        end
        | _, _ -> Error [ (expr'.loc, "TODO unsuported operation...") ])
  | UnaryOp (e, op) -> begin
    match op with
    | Minus -> begin
      match typecheck_expr ~force_const e env ctxt with
      | Error _ as err -> err
      | Ok { t_expr = IntTy; is_const } -> set_ty_info (IntTy, is_const)
      | Ok _ ->
        Error [ (expr'.loc, "TODO illegal argument for unary minus operator") ]
    end
    | Negation -> begin
      match typecheck_expr ~force_const e env ctxt with
      | Error _ as err -> err
      | Ok { t_expr = BoolTy; is_const } -> set_ty_info (BoolTy, is_const)
      | Ok _ -> Error []
    end
  end
  | EventRef id -> typecheck_event_ref_helper ~force_const id.data
  | Trigger label ->
    typecheck_event_ref_helper ~force_const:true label (*TODO add const*)
  | Record fields -> begin
    let fields_typecheck_res =
      fold_left_error
        (fun acc field -> typecheck_record_field_helper ~force_const field acc)
        ([], true)
        fields
    in
    match fields_typecheck_res with
    | Ok (field_types, all_fields_const) ->
      set_ty_info ~force_const (RecordTy field_types, all_fields_const)
    | Error _ as err -> err
  end
  | PropDeref (ref_expr', prop) ->
    let set_ty_info ?(force_const = None) (t_expr, is_const) expr' =
      let is_const =
        if Option.is_some force_const then Option.get force_const else is_const
      in
      let ty_info = { t_expr; is_const } in
      expr'.ty := Some ty_info;
      (ty_info, force_const)
    in
    (* set expr'.ty and ref_expr'.ty in the process, returning expr'.ty *)
    (* TODO revisit - initiator/receiver expressions not verified*)
    let rec deref_helper ?(force_const = None) expr' ref_expr' prop' =
      match ref_expr'.data with
      | PropDeref (ref_expr_1', prop_1') -> begin
        match deref_helper ~force_const ref_expr' ref_expr_1' prop_1' with
        | Ok ({ t_expr = EventTy label; _ }, force_const) -> begin
          match prop'.data with
          | "value" ->
            let label_ty_info =
              (Option.get !(StringMap.find label ctxt.event_types)).ty_info
            in
            (* mystical line... TODO explain better - inputs turn to non-const, unless already set *)
            let new_force_const =
              if Option.is_some force_const then force_const
              else Option.Some false
            in
            Ok
              (set_ty_info
                 ~force_const:new_force_const
                 (label_ty_info.t_expr, false)
                 ref_expr')
          | "initiator" -> Ok(set_ty_info (RecordTy [], true) ref_expr')
          | "receiver" -> Ok(set_ty_info (RecordTy [], true) ref_expr')
          | _ -> Error [ (prop'.loc, no_such_event_property prop') ]
        end
        | Ok ({ t_expr = EventRefTy (label, is_ref_to_const); _ }, force_const)
          -> begin
          match prop_1'.data with
          | "value" ->
            (* TODO revisit - should be getting false through event label ? maybe not *)
            let label_ty_info =
              (Option.get !(StringMap.find label ctxt.event_types)).ty_info
            in
            Ok
              (set_ty_info
                 ~force_const
                 (label_ty_info.t_expr, is_ref_to_const)
                 ref_expr')
          | "initiator" -> Ok(set_ty_info (RecordTy [], true) ref_expr')
          | "receiver" -> Ok(set_ty_info (RecordTy [], true) ref_expr')
          | _ -> Error [ (prop'.loc, no_such_event_property prop') ]
        end
        | Ok ({ t_expr = RecordTy ty_fields; _ }, force_const) -> begin
          let lookup_res =
            List.find_opt
              (fun { data = name, _; _ } -> name.data = prop'.data)
              ty_fields
          in
          match lookup_res with
          | None ->
            Error [ (prop'.loc, no_such_record_field expr' ref_expr' prop') ]
          | Some { data = _, ty_expr; _ } ->
            let ty_info = Option.get !(ty_expr.ty) in
            (* TODO ensure we're setting this right - test (due to const) *)
            (* ref_expr_1.ty := Some ty_info; *)
            Ok
              (set_ty_info
                 ~force_const
                 (ty_info.t_expr, ty_info.is_const)
                 expr')
        end
        | Ok ({ t_expr; _ }, _) ->
          Error [ (ref_expr'.loc, no_such_deref_property t_expr prop') ]
        | Error _ as err -> err
      end
      | EventRef id -> begin
        match prop'.data with
        | "value" ->
          (* fetch directly to retrieve 'const', which is specific to the event, not the type *)
          let event_node = get_event_node_by_id id in
          let event_label = (snd event_node.event'.data.info.data).data in
          let { t_expr; is_const } =
            Option.get !(event_node.event'.data.data_expr.ty)
          in
          let event_ref_ty = EventRefTy (event_label, is_const) in
          let ty_info, _ =
            set_ty_info ~force_const (event_ref_ty, is_const) ref_expr'
          in
          Ok (set_ty_info ~force_const (t_expr, is_const) expr')

        | "initiator" -> Ok(set_ty_info (RecordTy [], true) ref_expr')
        | "receiver" -> Ok(set_ty_info (RecordTy [], true) ref_expr')
        | _ -> Error [ (prop'.loc, no_such_event_property prop') ]
      end
      | Trigger label -> begin
        match prop'.data with
        | "value" ->
          (* fetch directly to retrieve 'const', which is specific to the event, not the type *)
          let event_node =
            get_event_node_by_id (annotate ~loc:ref_expr'.loc label)
          in
          let event_label = (snd event_node.event'.data.info.data).data in
          let { t_expr; is_const } =
            Option.get !(event_node.event'.data.data_expr.ty)
          in
          let event_ref_ty = EventRefTy (event_label, true) in
          let ty_info, _ =
            set_ty_info ~force_const (event_ref_ty, true) ref_expr'
          in
          Ok (set_ty_info ~force_const:(Some true) (t_expr, is_const) expr')
        | "initiator" -> Ok(set_ty_info (RecordTy [], true) ref_expr')
        | "receiver" -> Ok(set_ty_info (RecordTy [], true) ref_expr')
        | _ -> Error [ (prop'.loc, no_such_event_property prop') ]
      end
      | Record fields ->
        let lookup_res =
          List.find_opt
            (fun { data = name, _; _ } -> name.data = prop'.data)
            fields
        in
        begin
          match lookup_res with
          | None ->
            Error [ (prop'.loc, no_such_record_field expr' ref_expr' prop') ]
          | Some { data = _, expr; _ } ->
            (* Shouldn't we be typechecking this expr also? *)
            let ty_info = Option.get !(expr.ty) in
            Ok
              (set_ty_info
                 ~force_const
                 (ty_info.t_expr, ty_info.is_const)
                 ref_expr')
        end
      | _ -> Error [ (Nowhere, "") ]
    in
    begin
      match deref_helper expr' ref_expr' prop with
      | Ok (ty_info, _) -> Ok ty_info
      | Error _ as err -> err
    end
  | _ -> Error []

(* ============================================================================
 * == Errors
 * ========================================================================== *)

and on_err_equally_labelled_events_declare_different_types label'
    (t_expr : type_expr) (prev_t_expr : type_expr) =
  Printf.sprintf
    "Event with label '%s' has type '%s', but the choreography defines another \
     event with this label (with type '%s');\n\
    \  Data expressions of events with the same label must have equal types."
    label'.data
    (Frontend.Unparser.unparse_type t_expr)
    (Frontend.Unparser.unparse_type prev_t_expr)

and unknown_security_label_role role =
  Printf.sprintf "Reference to undeclared security label role'%s'" role.data

and unknown_participant_role role =
  Printf.sprintf "Reference to undeclared role'%s'" role

and on_err_unknown_named_param_in_sec_label role_label' unknown_named_param' =
  Printf.sprintf
    "Security label defines unknow named parameter '%s':\n\
     \t no such parameter in '%s's declaration -> %s"
    unknown_named_param'.data
    role_label'.data
    (string_of_loc role_label'.loc)

and unknown_participant_role_named_param role_label' unknown_named_param' =
  Printf.sprintf
    "Role label defines unknow named parameter '%s':\n\
     \t no such parameter in '%s's declaration -> %s"
    unknown_named_param'.data
    role_label'.data
    (string_of_loc role_label'.loc)

and on_err_named_param_left_undefined_in_sec_label role_label'
    undefined_named_param' =
  Printf.sprintf
    "Security label leaves named parameter '%s' undefined:\n\
     \t according to role '%s' declared here -> %s"
    undefined_named_param'.data
    role_label'.data
    (string_of_loc undefined_named_param'.loc)

and named_param_left_undefined_in_participant_label role_label'
    undefined_named_param' =
  Printf.sprintf
    "Paticipant label leaves named parameter '%s' undefined:\n\
     \t according to role '%s' declared here -> %s"
    undefined_named_param'.data
    role_label'.data
    (string_of_loc undefined_named_param'.loc)

and illegal_trigger_ref =
  "Illegal reference to '@trigger': can only be used inside a scope"

and no_such_deref_property type_expr prop =
  let open Frontend.Unparser in
  let ty_unparsed = unparse_type type_expr in
  Printf.sprintf
    "Unable to deref property: '%s' does not have an '.%s' property to deref"
    ty_unparsed
    prop.data

and no_such_event_property prop =
  Printf.sprintf
    "Events do not have a '%s' property (did you mean '.value'?)'"
    prop.data

and no_such_record_field expr ref_expr field_name =
  let open Frontend.Unparser in
  Printf.sprintf
    "> while typechecking expression '%s';\n\
    \ > '%s' evaluates to a record, but field '%s' is missing."
    (unparse_expr expr)
    (unparse_expr ref_expr)
    field_name.data

and unknown_event_reference event_id =
  Printf.sprintf "Reference to unknown event: '%s'" event_id.data

and reused_event_id_error nodes id uid _redeclaring_event =
  let node = List.assoc uid nodes in
  let err_msg =
    Printf.sprintf
      "Event id '%s' is reused within this scope.\n\
      \  (previously declared here %s)"
      id.data
      (string_of_loc node.event'.loc)
  in
  Error [ (id.loc, err_msg) ]

and redeclared_role prev_decl' =
  (* let _ = StringMap.find role.data value_dep_roles in *)
  let role, _ = prev_decl' in
  Printf.sprintf
    "Redeclared role: %s\n  previously declared here -> %s"
    role.data
  @@ string_of_loc role.loc

and duplicate_field_in_role_label role' previous_declaration =
  let role, _ = previous_declaration.data in
  Printf.sprintf
    "Role label '%s' redeclares field '%s':\n  (previously declared here -> %s)"
    role'
    role.data
    (string_of_loc role.loc)

(* TODO [adapt typing.ml to preprocessing_res] this conversion is temporary and
   should be deprecated *)
let ppx_res_to_typecheck_ctxt (ppx_res : Preprocessing.preprocessing_result) :
    typechecheck_context =
  let value_dep_roles = ppx_res.value_dep_roles
  and typecheck_graph =
    List.fold_left
      (fun acc ((uid, node) : element_uid * Preprocessing.event_node) ->
        let event' = node.event
        and data_dependency = node.data_dependency
        and uid_env = node.uid_env
        and userset_alias_types = node.userset_alias_types in
        (uid, { event'; data_dependency; uid_env; userset_alias_types }) :: acc)
      []
      (StringMap.bindings ppx_res.event_nodes_by_uid)
  and event_types =
    List.map
      (fun label -> (label, ref None))
      (StringSet.elements ppx_res.event_types)
    |> StringMap.of_list
  and relations = ppx_res.relations in
  { value_dep_roles (* ; uid_env = Env.empty *)
  ; typecheck_graph
  ; event_types
  ; relations
  }

let typecheck_ctxt_to_typecheck_res (ctxt : typechecheck_context) :
    typecheck_result =
  let event_nodes_by_uid : event_node StringMap.t =
    List.map
      (fun ((label, node) : event_ty * typecheck_node) ->
        let { event'; data_dependency; uid_env; userset_alias_types } = node in
        let event = event' in
        let res_node : event_node =
          { event; data_dependency; uid_env; userset_alias_types }
        in
        (label, res_node))
      ctxt.typecheck_graph
    |> StringMap.of_list
  and event_types =
    StringMap.map
      (fun label_opt_ref -> Option.get !label_opt_ref)
      ctxt.event_types
  and relations = ctxt.relations in
  let res : typecheck_result = { event_nodes_by_uid; event_types; relations } in
  res

(** Entry-point into this module: typechecks the program *)
let check_program (preprocessing_res : Preprocessing.preprocessing_result) =
  let (ctxt : typechecheck_context) =
    ppx_res_to_typecheck_ctxt preprocessing_res
  in
  let typecheck_res =
    typecheck_events
      { ctxt with typecheck_graph = List.rev ctxt.typecheck_graph }
    >>= fun ctxt ->
    typecheck_participant_exprs ctxt >>= fun ctxt ->
    typecheck_security_levels ctxt >>= fun ctxt -> typecheck_relations ctxt
  in
  (* TODO remove debugs, just result.fold *)
  match typecheck_res with
  | Ok ctxt ->
    (* debug_preprocessed_events ctxt.typecheck_graph;
    debug_relations ctxt.relations; *)
    Ok (typecheck_ctxt_to_typecheck_res ctxt)
  | Error err -> Error err
