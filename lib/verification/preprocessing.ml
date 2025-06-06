module StringMap = Map.Make (String)
module StringSet = Set.Make (String)
module Choreo = Frontend.Syntax
open Choreo
open Utils
open Utils.Results

(*
 Aggregator for information collected during preprocessing:
  = value_dep_roles = information collected from role decls.
  = uid_counter = ancillary counter to set element_uids for program nodes.
  = uid_env = running environment binding event ids to uids.
  = userset_alias_types_env = running environment binding param aliases with 
    declared types.
  = event_types = program labels appearing in the program.
  = typecheck_graph = binds event uids to event-specific info, such as data dependencies.
  = relations = keeps relations and respective closures for id -> uid mapping.
*)
(* TODO revisit event_types - move option to label info fields  *)
type preprocessing_context =
  { value_dep_roles :
      (identifier' * type_expr' named_param' StringMap.t) StringMap.t
  ; uid_counter : int ref
  ; uid_env : element_uid Env.t
  ; userset_alias_types_env : type_info Env.t
  ; event_types : StringSet.t
  ; event_nodes_by_uid : (element_uid * typecheck_node) list
  ; relations : (relation' * element_uid Env.t) list
  }

(* a node in the "typecheck graph".
   = event = the event itself.
   = uid_env = event's closure binding ids to uids.
   = type_dependencies = the labels whose type must known prior to typechecking
    the event.
   = event_dependencies = the events whose type must be known prior to
    typechecking the event.
   = userset_alias_types = closure, visible aliases and types.
*)
and typecheck_node =
  { event' : event'
  ; uid_env : element_uid Env.t
  ; type_dependencies : string list
  ; event_dependencies : string list
  ; userset_alias_types : type_info StringMap.t
  }

and data_dependency =
  | ValueDependency of StringSet.t
  | TypeDependency of StringSet.t

and event_node =
  { event : event'
  ; uid_env : element_uid Env.t
  ; data_dependency : data_dependency option
  ; userset_alias_types : type_info StringMap.t
  }

and preprocessing_result =
  { value_dep_roles :
      (identifier' * type_expr' named_param' StringMap.t) StringMap.t
  ; event_nodes_by_uid : event_node StringMap.t
  ; event_types : StringSet.t
  ; relations : (relation' * element_uid Env.t) list
  }

(* TODO refactor - duplicate in typing *)
(* ancillary *)
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

(* a global counter used to generate element_uids *)
let counter = ref 0

and fresh_name_of id counter =
  let fresh_name = Printf.sprintf "%s_%s" id (string_of_int !counter) in
  counter := !counter + 1;
  fresh_name

(** {i (tail recursive)} [preprocess_value_dep_role_decls context [R1; ...;Rn]]
    performs an initial {i well-formedness} validation of the
    parameterisable-role declarations [[R1; ...;Rn]] in the program's preamble,
    initializing the [context] in the process.

    A role declaration consists of a {i role label} and, optionally, a
    collection of {i named parameters} (declared in record-style
    [<param_name>:<param_value>]).

    Preprocessing enforces the following well-formedness rules:
    - roles are not redeclared (i.e., each label is associated with a single
      declaration).
    - within a single parameterised role, parameters must be associated with
      distinct names (much like record fields should have distinct names).

    Returns [Ok context], encapsulating the updated [context] update after a
    successfull validation, or an [Error err ] describing the issue. *)
let rec preprocess_value_dep_role_decls ctxt (decls : value_dep_role_decl' list)
    =
  let preprocess_value_dep_role_decl ctxt (decl' : value_dep_role_decl') =
    let value_dep_roles = ctxt.value_dep_roles
    and role', params = decl'.data in

    match StringMap.find_opt role'.data value_dep_roles with
    | Some prev_decl -> Error [ (role'.loc, redeclared_role prev_decl) ]
    | None ->
      let set_ty_info param' =
        let _, type_expr' = param'.data in
        let t_expr = type_expr'.data
        and is_const = false in
        param'.ty := Some { t_expr; is_const }
      in
      List.iter set_ty_info params;
      begin
        match
          to_string_map params (duplicate_field_in_role_label role'.data)
        with
        | Error _ as err -> err
        | Ok param_map ->
          let value_dep_roles =
            StringMap.add role'.data (role', param_map) value_dep_roles
          in
          Ok { ctxt with value_dep_roles }
      end
  in
  fold_left_error preprocess_value_dep_role_decl ctxt decls

and preprocess_flow_relations ~ctxt:{ value_dep_roles; _ } flow_relations =
  let process_flow_relation _acc { data = label_l, label_r; _ } =
    let sec_label_l = StringMap.find_opt label_l.data value_dep_roles
    and sec_label_r = StringMap.find_opt label_r.data value_dep_roles in
    match (sec_label_l, sec_label_r) with
    | None, _ -> Error [ (label_l.loc, unknown_security_label_role label_l) ]
    | _, None -> Error [ (label_r.loc, unknown_security_label_role label_r) ]
    | Some _, Some _ -> Ok ()
  in
  fold_left_error process_flow_relation () flow_relations

and preprocess_spawn_program ctxt { events; relations } =
  preprocess_events events ctxt >>= fun ctxt ->
  preprocess_relations relations ctxt >>= fun ctxt -> Ok ctxt

and increment_uid (pp_ctxt : preprocessing_context) =
  pp_ctxt.uid_counter := !(pp_ctxt.uid_counter) + 1;
  pp_ctxt

and preprocess_events events ctxt' =
  (* preprocess a single event *)
  let rec preprocess_event (ctxt, kinds) event' =
    let label = (snd event'.data.info.data).data in
    (* register the type if not yet encountered *)
    let event_types = StringSet.add label ctxt.event_types in
    preprocess_event_id ~ctxt event' >>= fun uid ->
    preprocess_security_level ~ctxt event' >>= fun () ->
    preprocess_participants ctxt event' >>= fun (ctxt, aliases) ->
    collect_event_dependencies ~ctxt event' >>= fun deps ->
    update_ctxt ~ctxt event' uid deps event_types aliases >>= fun ctxt ->
    event'.uid := Some uid;
    let ctxt = increment_uid ctxt in
    Ok (ctxt, kinds)
  (* assert whether a role-based expression (security label, userset role/user,...)
     conforms to an existing role declaration in the program's preamble;
     checks the role label and expected parameter names
     (typechecking is addressed later) *)
  and assert_role_decl_conformance :
      'a 'b.
         role_label'
      -> 'b annotated named_param' list
      -> (identifier' -> string)
      -> (role_label' -> identifier' -> string)
      -> (role_label' -> identifier' -> string)
      -> _ result =
   fun role'
       defined
       on_err_unknown_role
       on_err_unknown_param
       on_err_missing_param
     ->
    match StringMap.find_opt role'.data ctxt'.value_dep_roles with
    | None -> Error [ (role'.loc, on_err_unknown_role role') ]
    | Some (declared_role', declared_params) -> begin
      match to_string_map defined (fun _ -> "TODO this error message") with
      | Error _ as err -> err
      | Ok defined_params ->
        assert_expected_named_params
          role'
          declared_params
          defined_params
          (on_err_unknown_param declared_role')
          (on_err_missing_param declared_role')
    end
  (* assert whether a list of defined parameters conform with the ones declared;
     in particular, we currently do not allow leaving parameters undefined) *)
  and assert_expected_named_params :
      'a 'b.
         role_label'
      -> 'a named_param' StringMap.t
      -> 'b named_param' StringMap.t
      -> (identifier' -> string)
      -> (identifier' -> string)
      -> _ result =
   fun def_role' declared defined on_err_unknown_param on_err_missing_param ->
    let merger _key opt1 opt2 =
      match (opt1, opt2) with
      | None, Some _ ->
        let entry' = List.assoc _key (StringMap.bindings defined) in
        let param_name', _ = entry'.data in
        Some (Error [ (param_name'.loc, on_err_unknown_param param_name') ])
      | Some _, None ->
        let entry' = List.assoc _key (StringMap.bindings declared) in
        let param_name', _ = entry'.data in
        Some (Error [ (def_role'.loc, on_err_missing_param param_name') ])
      | _, _ -> None
    in
    match StringMap.choose_opt StringMap.(merge merger declared defined) with
    | None -> Ok ()
    | Some (_, err) -> err
  (* detect reused event ids within same scope  *)
  and preprocess_event_id ~ctxt:{ uid_env; event_nodes_by_uid = graph; _ }
      event' =
    let id = fst event'.data.info.data in
    match Env.find_flat_opt id.data uid_env with
    | Some uid -> reused_event_id_error graph id uid event'
    | None -> Ok (fresh_name_of id.data counter)
  (* assert whether the declared security labels conform to the declared roles with
     respect to naming only: role name and associated parameter names
     (exprs occuring in parameter values are typechecked later on) *)
  and preprocess_security_level ~ctxt:{ value_dep_roles; _ } event =
    let preprocess_security_label
        (sec_label' : sec_label_param' parameterisable_role') =
      let sec_label_role', named_params = sec_label'.data in
      assert_role_decl_conformance
        sec_label_role'
        named_params
        unknown_security_label_role
        on_err_unknown_named_param_in_sec_label
        on_err_named_param_left_undefined_in_sec_label
    in
    iter_left_error preprocess_security_label event.data.security_level.data
  (* assert whether all role-based expressions conform to the declared roles with
     respect to naming only: role name and associated parameter names
     (exprs occuring in parameter values are typechecked later on *)
  and preprocess_participants ctxt event' =
    (* preprocess a single participant *)
    let rec preprocess_participant_exprs user_set_expr' =
      match user_set_expr'.data with
      | RoleExpr role_based_expr' ->
        let role', named_params = role_based_expr'.data in
        assert_role_decl_conformance
          role'
          named_params
          unknown_security_label_role
          unknown_participant_role_named_param
          named_param_left_undefined_in_participant_label
      | Initiator _ | Receiver _ -> Ok ()
    (* TODO [refactor] init and rcv exprs turned out to be much more similar than
       initially expected *)
    and preprocess_initiator_expr (ctxt, aliases) initiator_expr' =
      let preprocess_initiator_expr_param role (ctxt, aliases) named_param' =
        let param_name', param_val' = named_param'.data in
        match param_val'.data with
        | Any ->
          Ok (ctxt, aliases)
          (* Error
             [ ( param_val'.loc
               , "TODO error func to flag illegal initiator expr param value '*'"
               )
             ] *)
        | RuntimeValue alias -> begin
          match alias with
          | None -> Ok (ctxt, aliases)
          | Some alias' ->
            if Option.is_some (StringMap.find_opt alias'.data aliases) then
              Error
                [ ( alias'.loc
                  , "TODO err-msg function: redeclaring existing alias" )
                ]
            else
              let _, decl_params = StringMap.find role ctxt.value_dep_roles in
              let ty_info = (StringMap.find param_name'.data decl_params).ty in
              let aliases =
                StringMap.add alias'.data (Option.get !ty_info) aliases
              in
              Ok (ctxt, aliases)
        end
        | Alias alias' ->
          if StringMap.mem alias'.data aliases then Ok (ctxt, aliases)
          else err_unknown_parameter_alias alias'
        | Expr expr' ->
          let rec is_trigger_deref = function
            | Trigger _ -> true
            | PropDeref (base', _) -> is_trigger_deref base'.data
            | _ -> false
          in
          begin
            match expr'.data with
            | True | False | IntLit _ | StringLit _ -> Ok (ctxt, aliases)
            | PropDeref (base', _) ->
              if is_trigger_deref base'.data then Ok (ctxt, aliases)
              else
                Error
                  [ ( expr'.loc
                    , "TODO err-msg-fun userset-param values can only \
                       reference @trigger in deref expressions" )
                  ]
            | EventRef id' ->
              if StringMap.mem id'.data aliases then Ok (ctxt, aliases)
              else err_unknown_parameter_alias id'
            | _ ->
              Error
                [ ( expr'.loc
                  , "TODO err-msg-fun invalid expression in userset-param \
                     value: can only refer to literals and @trigger-based \
                     value " )
                ]
          end
      in
      match initiator_expr'.data with
      | RoleExpr role_based_expr' ->
        let role', named_params = role_based_expr'.data in
        iter_left_error preprocess_participant_exprs [ initiator_expr' ]
        >>= fun () ->
        fold_left_error
          (preprocess_initiator_expr_param role'.data)
          (ctxt, aliases)
          named_params
      | Initiator event_id' | Receiver event_id' ->
        if Option.is_some (Env.find_flat_opt event_id'.data ctxt.uid_env) then
          Ok (ctxt, aliases)
        else Error [ (initiator_expr'.loc, "TODO err-msg-fun: no such event ") ]
    and preprocess_receiver_expr (ctxt, aliases) receiver_expr' =
      let preprocess_receiver_expr_param (ctxt, aliases) named_param' =
        let _, param_val' = named_param'.data in
        match param_val'.data with
        | RuntimeValue _ ->
          Error
            [ ( param_val'.loc
              , "TODO error func to flag illegal receiver expr param value \
                 '#<name_param>'" )
            ]
        | Alias alias' ->
          if StringMap.mem alias'.data aliases then Ok (ctxt, aliases)
          else err_unknown_parameter_alias alias'
            (* else Error [ (alias'.loc, "TODO err-msg-fun unknown param alias") ] *)
        | Expr expr' ->
          let rec is_trigger_deref = function
            | Trigger _ -> true
            | PropDeref (base', _) -> is_trigger_deref base'.data
            | _ -> false
          in
          begin
            match expr'.data with
            | True | False | IntLit _ | StringLit _ -> Ok (ctxt, aliases)
            | PropDeref (base', _) ->
              if is_trigger_deref base'.data then Ok (ctxt, aliases)
              else
                Error
                  [ ( expr'.loc
                    , "TODO err-msg-fun userset-param values can only \
                       reference @trigger in deref expressions" )
                  ]
            | EventRef id' ->
              if StringMap.mem id'.data aliases then Ok (ctxt, aliases)
              else err_unknown_parameter_alias id'
                (* else Error [ (id'.loc, "TODO err-msg-fun unknown param alias") ] *)
            | _ ->
              Error
                [ ( expr'.loc
                  , "TODO err-msg-fun invalid expression in userset-param \
                     value: can only refer to literals and @trigger-based \
                     value " )
                ]
          end
        (* | Expr _  *)
        | Any -> Ok (ctxt, aliases)
      in
      match receiver_expr'.data with
      | RoleExpr role_based_expr' ->
        let _, named_params = role_based_expr'.data in
        iter_left_error preprocess_participant_exprs [ receiver_expr' ]
        >>= fun () ->
        fold_left_error
          preprocess_receiver_expr_param
          (ctxt, aliases)
          named_params
      | Initiator event_id' | Receiver event_id' ->
        (* TODO assess refactoring out this bit - same for init and rcvrs *)
        if Option.is_some (Env.find_flat_opt event_id'.data ctxt.uid_env) then
          Ok (ctxt, aliases)
        else Error [ (receiver_expr'.loc, "TODO err-msg-fun: no such event ") ]
    in
    (* TODO revisit - code cleanup *)
    let aliases = Env.to_assoc_list ctxt'.userset_alias_types_env in
    let aliases =
      List.fold_left
        (fun map (name, value) -> StringMap.add name value map)
        StringMap.empty
        aliases
    in
    match event'.data.participants.data with
    | Local initiator' -> preprocess_initiator_expr (ctxt, aliases) initiator'
    | Interaction (initiator', receivers) ->
      preprocess_initiator_expr (ctxt, aliases) initiator'
      >>= fun (ctxt, aliases) ->
      fold_left_error preprocess_receiver_expr (ctxt, aliases) receivers
  and update_ctxt ~ctxt:{ uid_env; event_nodes_by_uid; _ } event' uid
      (type_dependencies, event_dependencies) event_types userset_alias_types =
    let id = fst event'.data.info.data in
    let uid_env = Utils.Env.bind id.data uid uid_env in
    let event_nodes_by_uid =
      ( uid
      , { event'
        ; type_dependencies
        ; event_dependencies
        ; uid_env
        ; userset_alias_types
        } )
      :: event_nodes_by_uid
    in
    Ok { ctxt' with uid_env; event_types; event_nodes_by_uid }
  in
  fold_left_error preprocess_event (ctxt', []) events >>= fun (ctxt, _) ->
  Ok ctxt

and preprocess_relations relations (ctxt' : preprocessing_context) =
  fold_left_error preprocess_relation ctxt' relations

(* Checks whether there are references to unknown events, collects relations
    for typechecking and handles scoping *)
and preprocess_relation ctxt relation =
  let uid_element = string_of_int !(ctxt.uid_counter) in
  relation.uid := Some uid_element;
  let ctxt = increment_uid ctxt
  and unknown_event_reference_err id =
    Error [ (id.loc, unknown_event_reference id) ]
  in
  let env = ctxt.uid_env in
  match relation.data with
  | ControlRelation (id1, guard, id2, _) -> begin
    match (Env.find_flat_opt id1.data env, Env.find_flat_opt id2.data env) with
    | None, _ -> unknown_event_reference_err id1
    | _, None -> unknown_event_reference_err id2
    | Some _, Some _ -> (
      (* TODO address guard dependencies *)
      match collect_expr_dependencies guard env with
      | Error err -> Error err
      | Ok _ -> Ok { ctxt with relations = (relation, env) :: ctxt.relations })
  end
  | SpawnRelation (id, trigger_label, guard, spawn_progr) -> (
    match Env.find_flat_opt id.data env with
    | None -> unknown_event_reference_err id
    | Some uid -> (
      (* TODO address guard dependencies *)
      match collect_expr_dependencies guard env with
      | Error err -> Error err
      | Ok _ -> (
        let ctxt =
          { ctxt with
            relations =
              (relation, env) :: ctxt.relations
              (* ; uid_env = Utils.Env.bind "@trigger" uid @@ Env.begin_scope env *)
          ; uid_env = Utils.Env.bind trigger_label uid @@ Env.begin_scope env
          }
        and type_aliases_map =
          (List.assoc uid ctxt.event_nodes_by_uid).userset_alias_types
        in
        (* TODO cleanup a bit *)
        let userset_alias_types_env =
          Env.begin_scope ctxt.userset_alias_types_env
        in
        let userset_alias_types_env =
          Env.bind_list
            (StringMap.bindings type_aliases_map)
            userset_alias_types_env
        in
        let ctxt = { ctxt with userset_alias_types_env } in
        match preprocess_spawn_program ctxt spawn_progr with
        | Error err -> Error err
        | Ok ctxt ->
          Ok
            { ctxt with
              userset_alias_types_env =
                Env.end_scope ctxt.userset_alias_types_env
            ; uid_env = Env.end_scope ctxt.uid_env
            })))

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

(* collect any dependencies on other events or their types: requires processing
   the event's security level, data expression and participants *)
and collect_event_dependencies ~ctxt:{ uid_env; _ } (event' : event') =
  (* collect any event references within the security level *)
  let collect_sec_level_dependencies =
    (* collect event references within a single security label's parameter *)
    let collect_param_deps acc sec_label_param' =
      let _, param = sec_label_param'.data in
      match param.data with
      | Parameterised expr' -> begin
        match collect_expr_dependencies expr' uid_env with
        | Error err -> Error err
        | Ok deps -> Ok (deps @ acc)
      end
      | _ -> Ok acc
    in
    (* collect any event references within a security label *)
    let collect_label_deps acc sec_label' =
      let _, params = sec_label'.data in
      fold_left_error collect_param_deps acc params
    in
    (* TODO <when stable> cleanup what was left behind from access control *)
    (* fold_left_error fold_helper [] event.data.access_ctrl >>= fun deps' -> *)
    fold_left_error collect_label_deps [] event'.data.security_level.data
  in
  let uniq l = List.sort_uniq String.compare l in
  collect_sec_level_dependencies >>= fun sec_deps ->
  match event'.data.data_expr.data with
  | Input type_expr ->
    Ok (uniq @@ collect_type_dependencies type_expr, uniq sec_deps)
  | Computation expr' ->
    collect_expr_dependencies expr' uid_env >>= fun expr_deps ->
    Ok ([], uniq (sec_deps @ expr_deps))

(** Collect EventId- and Trigger-related dependencies; checks whether all
    references (both trigger and event ids) are valid *)
and collect_expr_dependencies (expr' : expr') uid_env =
  let rec collect_deps deps exprs =
    match exprs with
    | [] -> Ok (List.sort_uniq String.compare deps)
    | expr :: rest -> begin
      match expr.data with
      | EventRef id' -> begin
        match Env.find_flat_opt id'.data uid_env with
        | None -> Error [ (id'.loc, unknown_event_reference id') ]
        | Some uid -> collect_deps (uid :: deps) rest
      end
      | Trigger label -> (
        match Env.find_flat_opt label uid_env with
        | None -> Error [ (expr.loc, illegal_trigger_ref) ]
        | Some uid -> collect_deps (uid :: deps) rest)
      | PropDeref (expr, _) -> collect_deps deps (expr :: rest)
      | Record fields ->
        let values = List.map (fun { data = _, value; _ } -> value) fields in
        collect_deps deps (values @ rest)
      | BinaryOp (e1, e2, _) -> collect_deps deps (e1 :: e2 :: rest)
      | UnaryOp (e1, _) -> collect_deps deps (e1 :: rest)
      | _ -> collect_deps deps rest
    end
  in
  collect_deps [] [ expr' ]

and collect_type_dependencies type_expr =
  let rec collect_aux acc type_exprs =
    match type_exprs with
    | [] -> List.sort_uniq String.compare acc
    | type_expr :: rest -> begin
      match type_expr with
      | EventTy ty -> collect_aux (ty :: acc) rest
      | RecordTy ty_fields ->
        collect_aux
          acc
          (List.append
             (List.map
                (fun { data = _, type_expr; _ } -> type_expr.data)
                ty_fields)
             rest)
      | _ -> collect_aux acc rest
    end
  in
  collect_aux [] [ type_expr.data ]

and check_missing_labels ctxt =
  let check_input_labels ctxt (uid, node) =
    let event' = node.event' in
    match event'.data.data_expr.data with
    | Computation _ -> Ok ctxt
    | Input _ ->
      let _, label' = event'.data.info.data in
      let node = List.assoc uid ctxt.event_nodes_by_uid in
      let check_label ctxt (label : event_label) =
        if StringSet.mem label ctxt.event_types then Ok ctxt
        else Error [ (label'.loc, "Missing label " ^ label) ]
      in
      fold_left_error check_label ctxt node.type_dependencies
  in
  fold_left_error check_input_labels ctxt ctxt.event_nodes_by_uid

(* ==========
   Errors
   ===========*)

and err_unknown_parameter_alias alias' =
  Error
    [ ( alias'.loc
      , Printf.sprintf
          "Unknown alias '%s': alias is not bound to any parameter in this \
           scope).\n\
          \  (requires a previous '<param> as %s' to be introduced in this \
           scope)"
          alias'.data
          alias'.data )
    ]

and unknown_event_reference event_id =
  Printf.sprintf "Reference to unknown event: '%s'" event_id.data

and redeclared_role prev_decl' =
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

and unknown_security_label_role role =
  Printf.sprintf "Reference to undeclared security label role'%s'" role.data

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
    "Participant label leaves named parameter '%s' undefined:\n\
     \t according to role '%s' declared here -> %s"
    undefined_named_param'.data
    role_label'.data
    (string_of_loc undefined_named_param'.loc)

and illegal_trigger_ref =
  "Illegal reference to '@trigger': can only be used inside a scope"

and preprocess_program (program : program) =
  let rec to_result (ctxt : preprocessing_context) =
    let event_nodes_by_uid =
      List.fold_left
        (fun acc (uid, node) ->
          let val_deps = node.event_dependencies
          and ty_deps = node.type_dependencies in
          let event = node.event'
          and uid_env = node.uid_env
          and data_dependency =
            if List.is_empty ty_deps then
              if List.is_empty val_deps then None
              else Some (ValueDependency (StringSet.of_list val_deps))
            else Some (TypeDependency (StringSet.of_list ty_deps))
          and userset_alias_types = node.userset_alias_types in
          StringMap.add
            uid
            { event; uid_env; data_dependency; userset_alias_types }
            acc)
        StringMap.empty
        ctxt.event_nodes_by_uid
    and value_dep_roles = ctxt.value_dep_roles
    and event_types = ctxt.event_types
    and relations = ctxt.relations in
    { event_nodes_by_uid; value_dep_roles; event_types; relations }
  in
  let ctxt =
    { value_dep_roles = StringMap.empty
    ; uid_counter = ref 0
    ; userset_alias_types_env = Env.empty
    ; uid_env = Env.empty
    ; event_nodes_by_uid = []
    ; event_types = StringSet.empty
    ; relations = []
    }
  in
  preprocess_value_dep_role_decls ctxt program.roles >>= fun ctxt ->
  preprocess_flow_relations ~ctxt program.security_lattice >>= fun () ->
  preprocess_spawn_program ctxt program.spawn_program >>= fun ctxt ->
  check_missing_labels ctxt >>= fun ctxt -> Ok (to_result ctxt)
