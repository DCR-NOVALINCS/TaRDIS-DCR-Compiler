module Choreo = Frontend.Syntax
open Choreo
open Sat
open Utils
open Utils.Results
open Userset_encoding
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let rec peek : 'a. 'a list -> 'a = fun stack -> List.hd stack

and pop : 'a. 'a list -> 'a * 'a list =
 fun stack -> (List.hd stack, List.tl stack)

and push : 'a. 'a -> 'a list -> 'a list = fun elem stack -> elem :: stack

and update_top : ('a -> 'a) -> 'a list -> 'a list =
 fun update stack ->
  let top, tl = pop stack in
  push (update top) tl

module RoleCtxt : sig
  type t =
    { role : CnfRole.t
    ; defines : binding_info StringMap.t
    ; uses : binding_info StringMap.t
    ; implicit_constraints : cnf_clause list
    }

  and binding_info =
    { leading_param : identifier
    ; renaming : string
    ; local_bind_expr' : expr'
    ; spawn_bind_expr' : expr'
    }

  val init_empty : role_label -> t

  val to_string : ?indent:string -> t -> string
end = struct
  type t =
    { role : CnfRole.t
    ; defines : binding_info StringMap.t
    ; uses : binding_info StringMap.t
    ; implicit_constraints : cnf_clause list
    }

  and binding_info =
    { leading_param : identifier
    ; renaming : string
    ; local_bind_expr' : expr'
    ; spawn_bind_expr' : expr'
    }

  let to_string ?(indent = "") (t : t) =
    let sprintf = Printf.sprintf in
    let rec binding_info_to_string (info : binding_info) =
      let leading_param = sprintf "leading_param: %s" info.leading_param
      and local_bind_expr =
        sprintf "local_bind_expr: %s"
        @@ Frontend.Unparser.unparse_expr info.local_bind_expr'
      and spawn_bind_expr =
        sprintf "spawn_bind_expr: %s"
        @@ Frontend.Unparser.unparse_expr info.spawn_bind_expr'
      in
      sprintf "{%s; %s; %s}" leading_param local_bind_expr spawn_bind_expr
    and uses_defines_to_string map =
      List.map
        (fun (k, v) -> sprintf "%s -> %s" k (binding_info_to_string v))
        (StringMap.bindings map)
      |> String.concat ", " |> sprintf "{%s}"
      (* and implicit_constraints_to_str lst =
      List.map
        (fun (k, v) -> sprintf "%s -> %s" k (binding_info_to_string v))
        (StringMap.bindings map)
      |> String.concat ", " |> sprintf "{%s}" *)
    in
    let role = sprintf "role: %s" @@ CnfRole.to_string t.role
    and uses = sprintf "uses: %s" @@ uses_defines_to_string t.uses
    and defines = sprintf "defines: %s" @@ uses_defines_to_string t.defines
    and implicit_constraints =
      sprintf
        "implicit_constraints: %s"
        (unparse_cnf_formula t.implicit_constraints)
    in
    sprintf
      "%s{ %s\n%s; %s\n%s; %s\n%s; %s\n%s}"
      indent
      role
      indent
      uses
      indent
      defines
      indent
      implicit_constraints
      indent

  let init_empty label =
    { role = { label; param_types = StringMap.empty; encoding = [] }
    ; defines = StringMap.empty
    ; uses = StringMap.empty
    ; implicit_constraints = []
    }
end

type projection_t =
  | Local of cnf_clause list
  | TxO of cnf_clause list * CnfUserset.t * Endpoint.user_set_expr' list
  | RxO of cnf_clause list * CnfUserset.t * Endpoint.user_set_expr' list
  | TxRx of
      (cnf_clause list * CnfUserset.t * Endpoint.user_set_expr' list)
      * (cnf_clause list * CnfUserset.t * Endpoint.user_set_expr' list)

(* TODO move somewhere else *)
module Projection = struct
  open Choreo

  type program =
    { events : event_t list
    ; relations : relation list
    }
  (* TODO revise whether implicit_bindings hasn't become irrelevant after parameterised triggers *)

  (* [] maintains a mapping of the bindings accumulated across
  scopes wich are visible to this event, and likewise, propagated to
  subsequent nested scopes (e.g., 'X' -> ('_@X0', _@trigger.initiator.cid)) *)

  (** An intermediate placeholder for event-related information required both
      during the projection process (most often, cnf-based) and for the
      generation of the projected endpoint event (most often, expr-based).

      [event'] choreography event associated with this endpoint-event.

      [uid] the uid of the choreography [event'] (redundant, kept for
      convenience)-

      [self] knowledge about the user with visibility to this event - as a role
      succesively unifies with events, either as an initiator and/or a receiver,
      the field accumulates implicit knowledge about the role which is
      subsequently propagated to potentially nested scopes (and monotonically
      narrowing the role towards a user in the process).

      [local_bindings] maintains a mapping for the bindings introduced by this
      event (e.g., 'X' -> ('_@X0', _@trigger.initiator.cid)); as the value of a
      binding is only known at runtime, the computation expression indicates how
      a reference to X should be evaluated in a nested scope derived from this
      event, based on how the _@trigger-event is expected to store this
      information (supports rewritting of binding symbols in the projected
      participant expressions).

      [implicit_bindings] the cnf-based encoding of the local_bindings
      introduced by this event; any spawn based on this event must implicitly
      propagate these bindings to the context of the nested scope.

      [instantiation_constraints] *)
  and event_t =
    { event' : Choreo.event'
    ; uid : identifier
    ; self : CnfRole.t
    ; local_bindings : (string * expr') StringMap.t
    ; implicit_bindings : cnf_clause list
    ; instantiation_constraints : cnf_formula
    ; instantiation_constraint_exprs : expr' list list
    ; communication : communication
    ; symbols : expr' StringMap.t
    ; label : identifier
    ; marking : Choreo.event_marking
    ; data_expr' : Choreo.data_expr'
    }

  and relation = expr' list list * relation_t

  and relation_t =
    | ControlFlowRelation of
        element_uid
        * (element_uid * event_id)
        * (element_uid * event_id)
        * relation_type
        * cnf_formula
      (* * CnfRole.t *)
    | SpawnRelation of string * element_uid * (element_uid * event_id) * program

  and communication =
    | Local
    | Tx of CnfUserset.t * Endpoint.user_set_expr' list
    | TxO of CnfUserset.t * Endpoint.user_set_expr' list
    | Rx of CnfUserset.t * Endpoint.user_set_expr' list
    | RxO of CnfUserset.t * Endpoint.user_set_expr' list

  and role_param = string * expr'

  and role_expr =
    | Role of role_label * role_param list
    | Initr of event_id
    | Rcvr of event_id

  let rec unparse_events ?(indent = "") (events : event_t list) =
    let rec unparse_event (e : event_t) =
      (* TODO move next indent somewhere else later on - proper unparser *)
      let next_indent = indent ^ "  " in
      let rec unparse_info () =
        let id', label' = e.event'.data.info.data in
        Printf.sprintf "(%s : %s)" id'.data label'.data
      and unparse_participants roles =
        StringMap.bindings roles
        |> List.map (fun (_, constrained_role) ->
               CnfRole.to_string constrained_role)
        |> String.concat ", "
      and unparse_communication = function
        | Local ->
          Printf.sprintf "[Local]\n%s%s" next_indent (CnfRole.to_string e.self)
        | Tx (receivers, rcv_set) | TxO (receivers, rcv_set) ->
          Printf.sprintf
            "[Tx]\n%s%s\n%s%s->  %s\n%s[Tx] @self -> "
            next_indent
            (CnfRole.to_string e.self)
            next_indent
            next_indent
            (unparse_participants receivers)
            next_indent
          (* (Frontend.Unparser.unparse_user_set_exprs rcv_set) *)
        | Rx (initiators, init_set) | RxO (initiators, init_set) ->
          Printf.sprintf
            "[Rx]\n%s%s\n%s%s->  %s\n%s[Rx]  -> @self"
            next_indent
            (unparse_participants initiators)
            next_indent
            next_indent
            (CnfRole.to_string e.self)
            next_indent
      (* (Frontend.Unparser.unparse_user_set_exprs init_set) *)
      and unparse_symbols () =
        List.map
          (fun (sym, expr') ->
            Printf.sprintf "%s:%s" sym (Frontend.Unparser.unparse_expr expr'))
          (StringMap.bindings e.symbols)
        |> String.concat ", " |> Printf.sprintf "(%s)"
      and unparse_instantiation_exprs () =
        let unparse_clause clause =
          List.map Frontend.Unparser.unparse_expr clause
          |> String.concat ", " |> Printf.sprintf "[%s]"
        in
        List.map unparse_clause e.instantiation_constraint_exprs
        |> String.concat ", " |> Printf.sprintf "[%s]"
      in
      Printf.sprintf
        "%s(uid:%s)  %s %s  %s\n%s@requires %s\n%s%s%s"
        indent
        e.uid
        (unparse_info ())
        (unparse_symbols ())
        (unparse_communication e.communication)
        indent
        (unparse_cnf_formula e.instantiation_constraints)
        indent
        indent
        (unparse_instantiation_exprs ())
    in
    List.map unparse_event events |> String.concat "\n\n"

  and unparse_relation ?(indent = "") = function
    | ( _
      , ControlFlowRelation
          (_uid, (src_uid, src_id), (target_uid, target_id), rel_type, self) )
      ->
      Printf.sprintf
        "%s(%s,%s) %s (%s,%s) %s"
        indent
        src_uid
        src_id
        (Frontend.Unparser.unparse_ctrl_flow_relation_type rel_type)
        target_uid
        target_id
        (unparse_cnf_formula self)
      (* (CnfRole.to_string self) *)
    | _, SpawnRelation (_trigger_id, _uid, (src_uid, src_id), projection) ->
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

  and unparse_projection ?(indent = "") ({ events; relations } : program) =
    let unparsed_events = unparse_events ~indent events
    and unparsed_relations = unparse_relations ~indent relations in
    if unparsed_relations = "" then unparsed_events
    else
      Printf.sprintf "%s\n%s;\n\n%s" unparsed_events indent unparsed_relations
end

module Symbols : sig
  val next_trigger_val_sym : unit -> string

  val encodes_trigger_val_sym : string -> bool

  val next_bind_sym : unit -> string

  val encode_param_name : identifier -> string

  val encodes_param_name : string -> bool

  val try_decode_param_name : string -> identifier option
end = struct
  let trigger_sym_val_prefix = "@V"

  let param_bind_sym_prefix = "@X"

  let param_name_prefix = "#"

  let next_int =
    let counter = ref 0 in
    fun () ->
      incr counter;
      !counter

  let rec next_trigger_val_sym () =
    Printf.sprintf "%s%d" trigger_sym_val_prefix @@ next_int ()

  and encodes_trigger_val_sym sym =
    String.starts_with ~prefix:trigger_sym_val_prefix sym

  (* and next_param_val_sym () =
    Printf.sprintf "%s%d" param_sym_val_prefix @@ next_int () *)

  and next_bind_sym () =
    Printf.sprintf "%s%d" param_bind_sym_prefix @@ next_int ()

  and encode_param_name identifier =
    Printf.sprintf "%s%s" param_name_prefix identifier

  and encodes_param_name identifier =
    String.starts_with ~prefix:param_name_prefix identifier

  and try_decode_param_name sym =
    let len = String.length sym - String.length param_name_prefix in
    if encodes_param_name sym then
      Some (String.sub sym (String.length param_name_prefix) len)
    else None
end

(** A stack-like structure designed to manage the chain of nested environments,
    that result from spawn-driven subgraphs, during the projection process for
    some target role. *)
module TriggerCtxt : sig
  type t

  (** An active environment associated with every (sub)graph element (i.e.,
      top-level and spawn-derived graphs alike) during the projection process
      for some target role.

      [self] reflects the accumulated knowledge constraining an abstract
      participant, whose role is currently the target of the projection process.
      In any give scope, the field is used to determine the events in which the
      participant may take part, and under which additional constraints (if
      any), thereby increasing the knowledge that is implicitly propagated to
      trigger-based nested scopes. Any sequence of transitions to
      increasingly-nested scopes is necessarily associated with a monotonically
      decreasing set of [self]-encoded participants.

      [trigger_chain] the sequence triggered events leading to the this scope.
  *)
  and scope =
    { self : CnfRole.t
    ; trigger_id : identifier
    ; implicit_bindings : cnf_clause list
    ; trigger_chain : (event_id * Projection.event_t) list
    ; trigger_symbols : string StringMap.t
    ; trigger_exprs_by_sym : expr' StringMap.t
    ; bindings : (string * expr') StringMap.t
    ; exprs_by_sym : expr' Env.t
    }

  val init : self:CnfRole.t -> role_decl':Choreo.value_dep_role_decl' -> t

  val current_scope : t -> scope

  val self : t -> CnfRole.t

  val lookup_binding : identifier -> t -> (string * expr') option

  val lookup_expr_by_sym : string -> t -> expr'

  val bindings : t -> (string * expr') StringMap.t

  val trigger_sym_of : expr' -> t -> t * string

  val triggerer : event_id -> t -> Projection.event_t

  val trigger_exprs : t -> expr' StringMap.t

  val initiators_of : event_id -> t -> CnfRole.t list

  val receivers_of : event_id -> t -> CnfRole.t list

  val begin_scope : identifier -> Projection.event_t -> t -> t

  val end_scope : t -> t
end = struct
  exception Internal_error of string

  type t = (event_id * scope) list

  and scope =
    { self : CnfRole.t
    ; trigger_id : identifier
    ; implicit_bindings : cnf_clause list
    ; trigger_chain : (event_id * Projection.event_t) list
    ; trigger_symbols : string StringMap.t
    ; trigger_exprs_by_sym : expr' StringMap.t
    ; bindings : (string * expr') StringMap.t
    ; exprs_by_sym : expr' Env.t
    }

  let bootstrap_event_id = "#bootstrap"

  and bootstrap_trigger_id = "_@trigger#_"

  let init ~(self : CnfRole.t) ~(role_decl' : Choreo.value_dep_role_decl') =
    (* Reminder: we assume that the runtime value of a participants' params
      can be queried at runtime through regular computation expressions 
      following the generic form '_@self.params.<param_name>' 
      (e.g., cid -> _@self.params.cid); *)

    (* The [exprs_by_sym] env is initialized with the above-described 
    expressions at top level, based on the role's declared parameters *)
    let exprs_by_sym =
      let encode_self_prop_deref_expr named_param' =
        let self_ref_expr = annotate (EventRef (annotate "_@self")) in
        let param_name', value' = named_param'.data in
        let type_info = Option.get !(value'.ty) in
        let val_deref_expr =
          annotate (PropDeref (self_ref_expr, annotate "params"))
        in
        annotate ~ty:(Some type_info) (PropDeref (val_deref_expr, param_name'))
      in
      let _, params = role_decl'.data in
      List.map
        (fun ({ data = param_name', _; _ } as named_param') ->
          ( Symbols.encode_param_name param_name'.data
          , encode_self_prop_deref_expr named_param' ))
        params
      |> fun bindings -> Env.empty |> Env.bind_list bindings
    in
    [ ( bootstrap_event_id
      , { self
        ; trigger_id = bootstrap_trigger_id
        ; implicit_bindings = []
        ; trigger_symbols = StringMap.empty
        ; trigger_chain = []
        ; trigger_exprs_by_sym = StringMap.empty
        ; bindings = StringMap.empty
        ; exprs_by_sym
        } )
    ]

  let current_scope (t : t) = snd (peek t)

  let self (t : t) = (snd (peek t)).self

  let trigger_sym_of expr' (t : t) =
    (* stringify a @trigger.prop1.prop2... expression *)
    let rec to_trigger_key ?(acc = "") = function
      | Trigger label -> Printf.sprintf "%s.%s" label acc
      | PropDeref (base', prop') ->
        to_trigger_key ~acc:(prop'.data ^ acc) base'.data
      | _ ->
        (* trusting that preprocessing prevents other patterns here *)
        raise (Internal_error "Expecting a @trigger expression.")
    in
    let trigger_key = to_trigger_key expr'.data in
    Option.fold
      (StringMap.find_opt trigger_key (snd (peek t)).trigger_symbols)
      ~none:
        (let sym = Symbols.next_trigger_val_sym () in
         let ( id
             , ({ trigger_symbols; trigger_exprs_by_sym; exprs_by_sym; _ } as
                scope) ) =
           peek t
         in
         let trigger_symbols = StringMap.add trigger_key sym trigger_symbols in
         let trigger_exprs_by_sym = StringMap.add sym expr' trigger_exprs_by_sym
         and exprs_by_sym = Env.bind sym expr' exprs_by_sym in
         let t =
           update_top
             (fun _ ->
               ( id
               , { scope with
                   trigger_symbols
                 ; trigger_exprs_by_sym
                 ; exprs_by_sym
                 } ))
             t
         in
         (t, sym))
      ~some:(fun sym -> (t, sym))

  let triggerer event_id t = List.assoc event_id (snd (peek t)).trigger_chain

  let bindings t = (snd @@ peek t).bindings

  let lookup_binding declared_sym t =
    StringMap.find_opt declared_sym (bindings t)

  let lookup_expr_by_sym (sym : string) (t : t) =
    Env.find_flat sym (current_scope t).exprs_by_sym

  let initiators_of (event_id : event_id) (t : t) =
    let scope = snd (peek t) in
    let trigger_event = List.assoc event_id scope.trigger_chain in
    match trigger_event.communication with
    | Local | Tx _ | TxO _ -> [ trigger_event.self ]
    | Rx (initiators, _) | RxO (initiators, _) ->
      StringMap.bindings initiators |> List.map snd

  let receivers_of (event_id : event_id) (t : t) =
    let scope = snd (peek t) in
    let trigger_event = List.assoc event_id scope.trigger_chain in
    match trigger_event.communication with
    | Local -> (* assume typechecking handled this (TODO) **) assert false
    | Tx (receivers, _) | TxO (receivers, _) ->
      StringMap.bindings receivers |> List.map snd
    | Rx _ | RxO _ -> [ trigger_event.self ]

  let trigger_exprs (t : t) = (snd (peek t)).trigger_exprs_by_sym

  let begin_scope (trigger_id : identifier) (trigger : Projection.event_t)
      (t : t) : t =
    let enclosing_scope = snd @@ peek t
    and event_id = (fst trigger.event'.data.info.data).data in
    let self = trigger.self
    and trigger_chain = (event_id, trigger) :: enclosing_scope.trigger_chain
    and trigger_symbols = StringMap.empty
    and trigger_exprs_by_sym = StringMap.empty
    and bindings =
      StringMap.union
        (fun _ v _ -> Some v)
        enclosing_scope.bindings
        trigger.local_bindings
    and implicit_bindings = trigger.implicit_bindings in
    let exprs_by_sym =
      Env.begin_scope enclosing_scope.exprs_by_sym
      |> Env.bind_list
           (StringMap.bindings trigger.local_bindings |> List.map snd)
    in
    (* debug *)
    (* print_endline
      (Utils.Env.to_string ~fmt:Frontend.Unparser.unparse_expr exprs_by_sym); *)
    push
      ( event_id
      , { self
        ; trigger_id
        ; trigger_chain
        ; trigger_symbols
        ; trigger_exprs_by_sym
        ; implicit_bindings
        ; bindings
        ; exprs_by_sym
        } )
      t

  let end_scope (t : t) : t = snd @@ pop t
end

module CommunicationCtxt : sig
  (** An ancillary placeholder for the information derived from processing a
      choreography event.

      [init_ctxt] cnf-derived information about the initiators

      [initiators] the initiator expression as declared in the choreography
      event

      [rcv_ctxt] cnf-derived information about the initiators

      [receivers] the receiver expression as declared in the choreography event

      [local_bindings] maps each locally-introduced binding to its corresponding
      renaming and spawn-generated computation expression (e.g., a declared
      param '#cid as X', could add an entry X -> (@X0, _@trigger.initiator.cid))
  *)
  type t =
    { init_ctxt : RoleCtxt.t StringMap.t
    ; initiators : user_set_expr' list
    ; rcv_ctxt : RoleCtxt.t StringMap.t
    ; receivers : user_set_expr' list
    ; local_bindings : (string * expr') StringMap.t
    }

  (** Generate the communication ctxt associated to the [participants] declared
      in the choreography event *)
  val of_communication_expr :
    event_id -> participants -> TriggerCtxt.t -> TriggerCtxt.t * t

  val to_string : t -> string
end = struct
  open Choreo

  type t =
    { init_ctxt : RoleCtxt.t StringMap.t
    ; initiators : user_set_expr' list
    ; rcv_ctxt : RoleCtxt.t StringMap.t
    ; receivers : user_set_expr' list
    ; local_bindings : (string * expr') StringMap.t
    }

  let to_string (t : t) =
    let sprintf = Printf.sprintf in
    let ctxt_map_to_str map =
      List.map
        (fun (k, v) ->
          sprintf "   %s:\n%s" k (RoleCtxt.to_string ~indent:"   " v))
        (StringMap.bindings map)
      |> String.concat "\n  ; " |> sprintf "%s"
    and local_bindings_to_str map =
      List.map
        (fun (k, (sym, expr')) ->
          sprintf "%s: (%s, %s)" k sym (Frontend.Unparser.unparse_expr expr'))
        (StringMap.bindings map)
      |> String.concat ", " |> sprintf "{%s}"
    in
    let init_ctxt = sprintf "init_ctxt:\n%s" @@ ctxt_map_to_str t.init_ctxt
    and rcv_ctxt = sprintf "rcv_ctxt:\n%s" @@ ctxt_map_to_str t.rcv_ctxt
    and local_bindings =
      sprintf "local_bindings: %s" @@ local_bindings_to_str t.local_bindings
    in
    sprintf "{ %s\n; %s\n; %s\n}" init_ctxt rcv_ctxt local_bindings

  let add_clause_ (cnf_role : CnfRole.t) (clause : cnf_clause) : CnfRole.t =
    { cnf_role with encoding = cnf_and cnf_role.encoding [ clause ] }

  (* TODO [revisit] (strategy and constants) *)
  (* Encode '_@self.params.<param>' prop-deref expr *)
  let encode_self_prop_deref_expr named_param' =
    let self_ref_expr = annotate (EventRef (annotate "_@self")) in
    let param_name', value' = named_param'.data in
    let type_info = Option.get !(value'.ty) in
    let val_deref_expr =
      annotate (PropDeref (self_ref_expr, annotate "params"))
    in
    annotate ~ty:(Some type_info) (PropDeref (val_deref_expr, param_name'))

  (* TODO [revisit] (strategy and constants) *)
  (* Encode '_@X0.value prop-deref expr *)
  let encode_self_prop_deref_expr named_param' =
    let self_ref_expr = annotate (EventRef (annotate "_@self")) in
    let param_name', value' = named_param'.data in
    let type_info = Option.get !(value'.ty) in
    let val_deref_expr =
      annotate (PropDeref (self_ref_expr, annotate "params"))
    in
    annotate ~ty:(Some type_info) (PropDeref (val_deref_expr, param_name'))

  (* TODO [revisit] (strategy and constants) *)
  (* Encode '_@trigger.initiator.<param>' prop-deref expr *)
  let encode_trigger_init_param_deref_expr event_id named_param' =
    let trigger_ref_expr' =
      annotate
        (EventRef (annotate (Frontend.Syntax.trigger_id_of_event_id event_id)))
    in
    let param_name', value' = named_param'.data in
    let type_info = Option.get !(value'.ty) in
    let init_deref_expr' =
      annotate (PropDeref (trigger_ref_expr', annotate "initiator"))
    in
    annotate ~ty:(Some type_info) (PropDeref (init_deref_expr', param_name'))

  let encode_param_expr (trigger_ctxt : TriggerCtxt.t)
      (local_bindings : (string * expr') StringMap.t)
      (named_param' : user_set_param_val' named_param') (param_sym : identifier)
      (expr' : expr') (role_ctxt : RoleCtxt.t) =
    let update_role ?(implicit = false) (clause : cnf_clause)
        (uses : RoleCtxt.binding_info StringMap.t) =
      let role, implicit_constraints =
        if implicit then
          (role_ctxt.role, clause :: role_ctxt.implicit_constraints)
        else
          ( { role_ctxt.role with encoding = clause :: role_ctxt.role.encoding }
          , role_ctxt.implicit_constraints )
      in
      { role_ctxt with role; uses; implicit_constraints }
    and uses = role_ctxt.uses in
    match expr'.data with
    | True ->
      ( trigger_ctxt
      , local_bindings
      , update_role [ Positive (CnfEq (param_sym, BoolLit true)) ] uses )
    | False ->
      ( trigger_ctxt
      , local_bindings
      , update_role [ Negative (CnfEq (param_sym, BoolLit false)) ] uses )
    | IntLit int_val ->
      ( trigger_ctxt
      , local_bindings
      , update_role [ Positive (CnfEq (param_sym, IntLit int_val)) ] uses )
    | StringLit str_val ->
      ( trigger_ctxt
      , local_bindings
      , update_role [ Positive (CnfEq (param_sym, StringLit str_val)) ] uses )
    | PropDeref _ ->
      (* trusting that preprocessing prevents other patterns here *)
      let trigger_ctxt, trigger_sym =
        TriggerCtxt.trigger_sym_of expr' trigger_ctxt
      in
      ( trigger_ctxt
      , local_bindings
      , update_role [ Positive (CnfSymEq (param_sym, trigger_sym)) ] uses )
    | EventRef binding' ->
      (* in this context, it encodes a binding *)
      begin
        match TriggerCtxt.lookup_binding binding'.data trigger_ctxt with
        | Some (alpha_renaming, _) ->
          (* just bind to whatever _@X0 is in this ctxt (may be redundant - check later) *)
          ( trigger_ctxt
          , local_bindings
          , update_role [ Positive (CnfSymEq (param_sym, alpha_renaming)) ] uses
          )
        | None ->
          (* must be a local binding *)
          let renaming, spawn_bind_expr' =
            StringMap.find binding'.data local_bindings
          in
          let implicit, uses =
            match StringMap.find_opt binding'.data role_ctxt.uses with
            | Some _ ->
              (* role already bound via previous param *)
              (false, uses)
            | None ->
              (* first use of this binding by this role *)
              let leading_param = param_sym in
              let local_bind_expr' = encode_self_prop_deref_expr named_param' in
              let (binding_info : RoleCtxt.binding_info) =
                { leading_param; renaming; local_bind_expr'; spawn_bind_expr' }
              in
              (true, StringMap.add binding'.data binding_info uses)
          in
          ( trigger_ctxt
          , local_bindings
          , update_role
              ~implicit
              [ Positive (CnfSymEq (param_sym, renaming)) ]
              uses )
      end
    | _ -> assert false

  let encode_named_param event_id
      ((trigger_ctxt, role_ctxt, local_bindings) :
        TriggerCtxt.t * RoleCtxt.t * (string * expr') StringMap.t)
      (named_param' : user_set_param_val' named_param') =
    (* update role's param_types to reflect the [named_param'] *)
    let encode_param_ty named_param' (role_ctxt : RoleCtxt.t) =
      let param_name', value' = named_param'.data in
      let param_ty = (Option.get !(value'.ty)).t_expr in
      let param_types =
        StringMap.add param_name'.data param_ty role_ctxt.role.param_types
      in
      let role = { role_ctxt.role with param_types } in
      { role_ctxt with role }
    in
    let role_ctxt = encode_param_ty named_param' role_ctxt in
    let param_name', value' = named_param'.data in
    let param_sym = Symbols.encode_param_name param_name'.data in
    match value'.data with
    | Any -> (trigger_ctxt, local_bindings, role_ctxt)
    | Expr expr' ->
      encode_param_expr
        trigger_ctxt
        local_bindings
        named_param'
        param_sym
        expr'
        role_ctxt
    | Alias _identifier' ->
      (* TODO resolve this - param=alias is actually encoded as Expr of expr' 
      above: possible cleanup and remove *)
      assert false
    | RuntimeValue alias_opt' -> begin
      (* TODO [revisit] no longer an Option - None encoded to Any *)
      match alias_opt' with
      | None -> assert false
      | Some bind_sym' ->
        (* if we are here, param defines a new binding *)
        (* update local bindings and implicit_constraints *)
        let ((renaming, spawn_bind_expr') as bind_val) =
          ( Symbols.next_bind_sym ()
          , encode_trigger_init_param_deref_expr event_id named_param' )
        in
        (* update role_ctxt.defines *)
        let leading_param = param_sym
        and local_bind_expr' = encode_self_prop_deref_expr named_param' in
        let (binding_info : RoleCtxt.binding_info) =
          { leading_param; renaming; local_bind_expr'; spawn_bind_expr' }
        in
        let clause = [ Positive (CnfSymEq (param_sym, renaming)) ] in
        let defines =
          StringMap.add bind_sym'.data binding_info role_ctxt.defines
        and implicit_constraints = clause :: role_ctxt.implicit_constraints in
        let role_ctxt = { role_ctxt with defines; implicit_constraints } in
        let local_bindings =
          StringMap.add bind_sym'.data bind_val local_bindings
        in
        (trigger_ctxt, local_bindings, role_ctxt)
    end

  let user_set_role_expr_to_role_ctxt event_id
      ((trigger_ctxt, local_bindings) :
        TriggerCtxt.t * (string * expr') StringMap.t)
      (role_expr' : userset_role_expr') =
    let role', params = role_expr'.data in
    List.fold_left
      (fun (trigger_ctxt, local_bindings, role_ctxt) named_param' ->
        encode_named_param
          event_id
          (trigger_ctxt, role_ctxt, local_bindings)
          named_param')
      (trigger_ctxt, local_bindings, RoleCtxt.init_empty role'.data)
      params

  let encode_user_set_expr event_id (trigger_ctxt, local_bindings)
      user_set_expr' =
    let to_role_ctxts cnf_roles =
      List.map
        (fun role ->
          ({ role
           ; uses = StringMap.empty
           ; defines = StringMap.empty
           ; implicit_constraints = []
           }
            : RoleCtxt.t))
        cnf_roles
    in
    match user_set_expr'.data with
    | RoleExpr role_expr' ->
      user_set_role_expr_to_role_ctxt
        event_id
        (trigger_ctxt, local_bindings)
        role_expr'
      |> fun (a, b, c) -> (a, b, [ c ])
    | Initiator event_id' ->
      let init_ctxt =
        TriggerCtxt.initiators_of event_id'.data trigger_ctxt |> to_role_ctxts
      in
      (trigger_ctxt, local_bindings, init_ctxt)
    | Receiver event_id' ->
      let rcv_ctxt =
        TriggerCtxt.receivers_of event_id'.data trigger_ctxt |> to_role_ctxts
      in
      (trigger_ctxt, local_bindings, rcv_ctxt)

  let encode_user_set_exprs event_id (trigger_ctxt, local_bindings)
      user_set_exprs =
    List.fold_left
      (fun (trigger_ctxt, local_bindings, role_ctxts) user_set_expr' ->
        let trigger_ctxt, local_bindings, roles =
          encode_user_set_expr
            event_id
            (trigger_ctxt, local_bindings)
            user_set_expr'
        in
        ( trigger_ctxt
        , local_bindings
        , List.fold_left
            (fun roles_ctxts role_ctxt ->
              match
                StringMap.find_opt role_ctxt.RoleCtxt.role.label role_ctxts
              with
              | None ->
                StringMap.add
                  role_ctxt.RoleCtxt.role.label
                  role_ctxt
                  roles_ctxts
              | Some (prev : RoleCtxt.t) ->
                if
                  StringMap.is_empty prev.uses
                  && StringMap.is_empty prev.defines
                then
                  let role = CnfRole.union prev.role role_ctxt.role in
                  StringMap.add
                    role_ctxt.role.label
                    { prev with role }
                    roles_ctxts
                else
                  assert
                    (* not supporting multiple roles when using bindings *)
                    (* TODO cleanup *)
                    false)
            role_ctxts
            roles ))
      (trigger_ctxt, local_bindings, StringMap.empty)
      user_set_exprs

  let of_communication_expr event_id (participants : Choreo.participants)
      (trigger_ctxt : TriggerCtxt.t) : TriggerCtxt.t * t =
    let trigger_ctxt, local_bindings, init_ctxt, rcv_ctxt, initiators, receivers
        =
      ( participants |> function
        | Choreo.Local init' -> (init', [])
        | Choreo.Interaction (init', recvrs) -> (init', recvrs) )
      |> fun (initrs, rcvrs) ->
      let trigger_ctxt, local_bindings, initiators =
        encode_user_set_exprs
          event_id
          (trigger_ctxt, StringMap.empty)
          [ initrs ]
      in
      let trigger_ctxt, local_bindings, receivers =
        encode_user_set_exprs event_id (trigger_ctxt, local_bindings) rcvrs
      in
      (trigger_ctxt, local_bindings, initiators, receivers, [ initrs ], rcvrs)
    in
    ( trigger_ctxt
    , { local_bindings; init_ctxt; rcv_ctxt; initiators; receivers } )
end

(** [list_combine f [a1; ...; an] [b1; ...; bm]] returns the list
    [[f a1 b1; f a1 b2; ...; f an bm]], resulting from applying function [f] to
    each element in the cartesian product of [[a1; ...; an]] and
    [[b1; ...; bm]]. *)
let list_combine : 'a 'b 'c. ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list =
 fun combinator l1 l2 ->
  List.concat (List.map (fun l1 -> List.map (fun l2 -> combinator l1 l2) l2) l1)
(* 
module Event : sig
  (** [event'] base event as specified in the choreography.

      [uid] unique identifier derived from the base [event']'s uid to account
      the existence of dual events.

      [self] specifies the user-the that instantiating this event.

      [marking] derived from the base [event']'s marking, to account for the
      rx/tx-specific rules for handling the event marking, namely, its initial
      state.

      [communication] describes the communication, if any, triggered by the
      execution of this event (local/tx/rx)

      [symbols] symbolic identifiers associated to trigger-based exprs used by
      this event; symbols are used for encoding and are propagated into spawn
      scopes triggered by the event; the mapping is later used to recover the
      computation expressions back to generate the proper runtime instantiation
      constraints. *)
  type t =
    { event' : event'
    ; uid : identifier
    ; self : CnfRole.t
    ; marking : event_marking
    ; communication : communication
    ; symbols : expr' StringMap.t
    }

  and communication =
    | Local
    | Tx of CnfUserset.t
    | Rx of CnfUserset.t
end = struct
  open Choreo

  type t =
    { event' : event'
    ; uid : identifier
    ; self : CnfRole.t
    ; marking : Choreo.event_marking
    ; communication : communication
    ; symbols : expr' StringMap.t
    }

  and communication =
    | Local
    | Tx of CnfUserset.t
    | Rx of CnfUserset.t
end *)

(* Indicates whether a constrained role encodes a single user.

   Observation: a user has every role parameter constrained to either
   a value (e.g., [#p1=2]) or a "trigger" symbol (e.g., [#p1=@V3], and
   @V3=@trigger.value). Runtime aliases (e.g., '#p1 as X') can
   introduce constraints of the form [#p1 = #p2]) but these carry different
   semantics ("shape constraints").
*)
let rec is_user ({ param_types; encoding; _ } : CnfRole.t) =
  let binds_param param_sym = function
    | [ Positive (CnfSymEq (s1, s2)) ] ->
      (s1 = param_sym && not (Symbols.encodes_param_name s2))
      || (s2 = param_sym && not (Symbols.encodes_param_name s1))
    | [ Positive (CnfEq (s, _)) ] -> s = param_sym
    | _ -> false
  in
  List.for_all
    (fun param_sym -> List.exists (binds_param param_sym) encoding)
    (StringMap.bindings param_types
    |> List.map (fun x -> Symbols.encode_param_name @@ fst x))
(* TODO deprecate *)
(* List.fold_left
    (fun acc param ->
      let param_sym = Symbols.encode_param_name param in
      acc
      && List.exists
           (function
             | [ Positive (CnfSymEq (s1, s2)) ] ->
               (s1 = param_sym && not (Symbols.encodes_param_name s2))
               || ((not (Symbols.encodes_param_name s1)) && s2 = param_sym)
             | [ Positive (CnfEq (s, _)) ] -> param_sym = s
             | _ -> false)
           cnf)
    true
    (StringMap.bindings params |> List.map fst) *)

module ProjectionContext = struct
  (*
  _____________
  abstract_self : symbolic representation of the runtime participant;
  > e.g., P(p1=@s0; p2=@s1), with @s0=@self.value.p1, @s1=@self.value.p2
  __________
  projection
  __________
  a stack-like structure to build a projection as scopes are traversed
  ___________________
  symbols_by_elem_uid
  ===================
  binds event uids to the trigger-driven symbols introduced by their userset
  exprs - with each spawn, the triggering event adds its symbols to the 
  top-level context
  _____________________________
  control_flow_candidates_stack
  =============================
  stacks the control-flow relations of each scope on the recursion's way "down",
  delaying its processing to when the recursion bottoms
  *)

  (* TODO [refactoring/tentative] partition context.t into envs, stacks and globals *)
  type t =
    { role_decl' : Choreo.value_dep_role_decl'
    ; abstract_self : CnfRole.t
    ; ifc_constraints_by_uid : expr' StringMap.t
    ; trigger_ctxt : TriggerCtxt.t
    ; projection : Projection.program list
    ; projected_events_env : Projection.event_t list Env.t
    ; sourcing_rx_relations_by_uid :
        ((element_uid * event_id) * relation_type * cnf_formula) list
        StringMap.t
          (* ((element_uid * event_id) * relation_type * CnfRole.t) list StringMap.t *)
    }

  (* let mk_abstract_self (self : CnfRole.t) : CnfRole.t = *)
  let mk_abstract_self (label : Choreo.role_label) : CnfRole.t =
    (* let label = self.label *)
    let param_label = "@self"
    and param_val = Sat.BoolLit true in
    let param_types = StringMap.empty |> StringMap.add param_label BoolTy
    and encoding = [ [ Positive (CnfEq (param_label, param_val)) ] ] in
    { label; param_types; encoding }

  let init (ifc_constraints_by_uid : expr' StringMap.t)
      (role_decl' : Choreo.value_dep_role_decl') =
    let role_decl' = role_decl'
    and self = CnfRole.of_role_decl ~role_decl' in
    (* add "abstract-self" marker to self's encoding *)
    let abstract_self = mk_abstract_self (fst role_decl'.data).data in
    let trigger_ctxt =
      TriggerCtxt.init
        ~self:{ self with encoding = abstract_self.encoding }
        ~role_decl'
    and (projection : Projection.program list) =
      [ { events = []; relations = [] } ]
    and projected_events_env = Env.empty
    and sourcing_rx_relations_by_uid = StringMap.empty in
    { role_decl'
    ; abstract_self
    ; ifc_constraints_by_uid
    ; trigger_ctxt
    ; projection
    ; projected_events_env
    ; sourcing_rx_relations_by_uid
    }

  let self (t : t) = (TriggerCtxt.current_scope t.trigger_ctxt).self

  let projection (ctxt : t) = List.hd ctxt.projection

  let add_rx_sourced_relation (ctxt : t) scr_uid rel_info =
    let sourcing_rx_relations_by_uid =
      let rel_info =
        rel_info
        :: (StringMap.find_opt scr_uid ctxt.sourcing_rx_relations_by_uid
           |> Option.fold ~none:[] ~some:Fun.id)
      in
      StringMap.add scr_uid rel_info ctxt.sourcing_rx_relations_by_uid
    in
    { ctxt with sourcing_rx_relations_by_uid }

  let rx_sourced_with_uid_find_opt (ctxt : t) uid =
    StringMap.find_opt uid ctxt.sourcing_rx_relations_by_uid

  let projections_find_opt (event_id : event_id) (ctxt : t) =
    Env.find_flat_opt event_id ctxt.projected_events_env

  let include_projected_event (event_id : identifier)
      (projections : Projection.event_t list) (ctxt : t) =
    let hd_projection = List.hd ctxt.projection in
    let events = projections @ hd_projection.events in
    let hd_projection = { hd_projection with events } in
    let projection = hd_projection :: List.tl ctxt.projection
    (* update ancillary env to keep track of event "unfolding"
       (due to mutually-exclusive constraint groups) *)
    and projected_events_env =
      Env.bind event_id projections ctxt.projected_events_env
    in
    { ctxt with projection; projected_events_env }

  let add_relation (ctxt : t) (relation : Projection.relation) =
    let hd_projection = List.hd ctxt.projection in
    let relations = relation :: hd_projection.relations in
    let hd_projection = { hd_projection with relations } in
    let projection = hd_projection :: List.tl ctxt.projection in
    { ctxt with projection }

  (* TODO deprecate *)

  (** Store a ctrl-flow relation seen at this level (on the recursion's way
      down) *)
  (* let push_ctrl_flow_relation (relation : Projection.relation) (ctxt : t) =
    let top = relation :: List.hd ctxt.control_flow_candidates_stack in
    let control_flow_candidates_stack =
      top :: List.tl ctxt.control_flow_candidates_stack
    in
    { ctxt with control_flow_candidates_stack } *)

  let begin_scope (trigger_id : identifier) (trigger : Projection.event_t)
      (ctxt : t) =
    let trigger_ctxt =
      TriggerCtxt.begin_scope trigger_id trigger ctxt.trigger_ctxt
    and (projection : Projection.program list) =
      { events = []; relations = [] } :: ctxt.projection
    (* new scope to accumulate projected events - used to decide the relations
    to project TODO [revise] *)
    and projected_events_env = Env.begin_scope ctxt.projected_events_env in
    { ctxt with trigger_ctxt; projection; projected_events_env }

  let end_scope (ctxt : t) =
    let trigger_ctxt = TriggerCtxt.end_scope ctxt.trigger_ctxt
    and projection = List.tl ctxt.projection
    and projected_events_env = Env.end_scope ctxt.projected_events_env in
    { ctxt with trigger_ctxt; projection; projected_events_env }
end

(* 
  Rewrite user-set exprs replacing param bindings according to [bindings]
  
  @assumes. [bindings] stores the correct expr for every binding in 
  [user_set_expr'] (local- and scope-bindings alike)
*)
let rewrite_userset (bindings : expr' StringMap.t)
    (user_set_expr' : Choreo.user_set_expr') : Endpoint.user_set_expr' =
  (* (aux) rewrites a single user-set param *)
  let rewrite_user_set_param
      (user_set_param' : user_set_param_val' named_param') :
      Endpoint.user_set_param_val' named_param' =
    let rewrite_user_set_param_val = function
      | Expr expr' -> begin
        match expr'.data with
        | EventRef binding' ->
          (* (reminder) EventRef reflects a binding in this context *)
          Endpoint.Expr (StringMap.find binding'.data bindings)
        | _ -> Endpoint.Expr expr'
      end
      | RuntimeValue binding_opt ->
        (* (reminder) Option is guaranteed to be Some - syntax will eventually 
          be adjusted to prevent this redundancy - however, a binding introduced 
      on the rhs might not be used on the lhs - in that case, replace with Any *)
        let sym = (Option.get binding_opt).data in
        Option.fold
          (StringMap.find_opt sym bindings)
          ~none:Endpoint.Any
          ~some:(fun expr' -> Endpoint.Expr expr')
      | Any -> Endpoint.Any
      | Alias _ -> Endpoint.Any
    in
    (* actual update named-param's data *)
    let param_name', param_val' = user_set_param'.data in
    { user_set_param' with
      data =
        ( param_name'
        , { param_val' with data = rewrite_user_set_param_val param_val'.data }
        )
    }
  in
  match user_set_expr'.data with
  | Choreo.Initiator event_id' ->
    annotate ~ty:!(user_set_expr'.ty) (Endpoint.Initiator event_id')
  | Choreo.Receiver event_id' ->
    annotate ~ty:!(user_set_expr'.ty) (Endpoint.Receiver event_id')
  | RoleExpr userset_role_expr' ->
    let role_label', params = userset_role_expr'.data in
    { user_set_expr' with
      data =
        RoleExpr
          { userset_role_expr' with
            data = (role_label', List.map rewrite_user_set_param params)
          }
    }

let extract_min_diff_constraint_set (initial_encoding : cnf_formula)
    (final_encoding : cnf_formula) =
  (* print_endline @@ Printf.sprintf "\n\nextract_min_diff_constraint_set \
  called with\n  init= %s\n  final=%s"
  (unparse_cnf_formula initial_encoding)
  (unparse_cnf_formula final_encoding); *)
  let new_constraints =
    List.filter
      (fun c1 -> not @@ List.exists (fun c2 -> c1 = c2) initial_encoding)
      final_encoding
    |> List.sort_uniq cnf_clause_compare
  in
  List.fold_left
    (fun (base, acc) clause ->
      (* print_endline @@ Printf.sprintf "base=%s  acc=%s  clause=%s"
      (unparse_cnf_formula base)
      (unparse_cnf_formula acc)
      (unparse_cnf_formula [clause])
      ; *)
      if Sat.cnf_entails (base @ acc) clause then (base, acc)
      else (base, clause :: acc))
    (initial_encoding, [])
    new_constraints
  |> snd

let to_instantiation_constraint_exprs (instantiation_constraints : cnf_formula)
    (trigger_ctxt : TriggerCtxt.t) =
  let map_sym sym = TriggerCtxt.lookup_expr_by_sym sym trigger_ctxt in
  let map_cnf_bool_constraint ~(eq : bool) = function
    | CnfSymEq (sym1, sym2) ->
      let expr1', expr2' = (map_sym sym1, map_sym sym2) in
      if eq then
        annotate
          ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
          (Choreo.BinaryOp (expr1', expr2', Choreo.Eq))
      else
        annotate
          ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
          (Choreo.BinaryOp (expr1', expr2', Choreo.NotEq))
    | CnfEq (sym, lit_val) ->
      let expr' = map_sym sym in
      let sym_expr' =
        match lit_val with
        | BoolLit bool_val ->
          if bool_val then
            annotate
              ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true })
              Choreo.True
          else
            annotate
              ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true })
              Choreo.False
        | IntLit int_val ->
          annotate
            ~ty:(Some { t_expr = Choreo.IntTy; is_const = true })
            (Choreo.IntLit int_val)
        | StringLit str_val ->
          annotate
            ~ty:(Some { t_expr = Choreo.StringTy; is_const = true })
            (Choreo.StringLit str_val)
      in
      if eq then
        annotate
          ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
          (Choreo.BinaryOp (expr', sym_expr', Choreo.Eq))
      else
        annotate
          ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
          (Choreo.BinaryOp (expr', sym_expr', Choreo.NotEq))
  in
  List.map
    (List.map (function
      | Positive x -> map_cnf_bool_constraint ~eq:true x
      | Negative x -> map_cnf_bool_constraint ~eq:false x))
    instantiation_constraints

let rec project_spawn_program ctxt
    ({ events; relations } : Choreo.spawn_program) =
  project_events ctxt events |> fun ctxt -> project_relations ctxt relations

and project_events ctxt (events : Choreo.event' list) : ProjectionContext.t =
  (* *)
  let rec project (ctxt : ProjectionContext.t) (event' : Choreo.event')
      ~(self : CnfRole.t) ~(projection_type : projection_t)
      ~(local_bindings : (string * expr') StringMap.t) : Projection.event_t list
      =
    let base = event'.data in
    let uid = Option.get !(event'.uid)
    and label = (snd @@ base.info.data).data
    and data_expr' = base.data_expr
    (* reminder: the marking must eventually be adjusted according to direct
    dependencies - an Rx is usually not excluded or pending, unless
    it represents a direct dep. to other events initialized by @self *)
    and marking = base.marking.data
    and base_self = ProjectionContext.self ctxt in
    let trigger_ctxt = ctxt.ProjectionContext.trigger_ctxt in

    (* and marking = event'.data.marking.data in *)
    (*  *)
    let symbols =
      TriggerCtxt.trigger_exprs ctxt.ProjectionContext.trigger_ctxt
    in
    (* TODO revise - move constants *)
    let (res : Projection.event_t list) =
      begin
        match projection_type with
        | Local implicit_constraints ->
          [ (uid, implicit_constraints, Projection.Local) ]
        | TxO (implicit_constraints, receivers, rcv_set) ->
          [ ( uid ^ "_TxO"
            , implicit_constraints
            , Projection.TxO (receivers, rcv_set) )
          ]
        | RxO (implicit_constraints, initiators, init_set) ->
          [ ( uid ^ "_RxO"
            , implicit_constraints
            , Projection.RxO (initiators, init_set) )
          ]
        | TxRx
            ( (tx_implicit_constraints, receivers, rcv_set)
            , (rx_implicit_constraints, initiators, init_set) ) ->
          [ ( uid ^ "_Tx"
            , tx_implicit_constraints
            , Projection.Tx (receivers, rcv_set) )
          ; ( uid ^ "_Rx"
            , rx_implicit_constraints
            , Projection.Rx (initiators, init_set) )
          ]
      end
      |> List.map
           (fun (uid, implicit_bindings, communication) : Projection.event_t ->
             (* keep instantiation constraints down to new-knowledge only (i.e., 
                to whatever was not already entailed by @self) *)
             let instantiation_constraints =
               extract_min_diff_constraint_set base_self.encoding self.encoding
               |> List.filter (fun c1 ->
                      not @@ List.exists (fun c2 -> c1 = c2) implicit_bindings)
               |> List.sort_uniq cnf_clause_compare
             in

             (* debug *)
             (* print_endline
             @@ Printf.sprintf
                  "\n\
                   Call to project with:\n\
                  \  > base_self:\t\t%s\n\
                  \  > self:\t\t%s\n\
                  \  > inst. constraints:\t%s\n"
                  (CnfRole.to_string base_self)
                  (CnfRole.to_string self)
                  (unparse_cnf_formula @@ instantiation_constraints); *)

             (* TODO [revisit :: move somewhere else] *)
             let instantiation_constraint_exprs =
               let map_sym sym =
                 TriggerCtxt.lookup_expr_by_sym sym trigger_ctxt
               in
               let map_cnf_bool_constraint ~(eq : bool) = function
                 | CnfSymEq (sym1, sym2) ->
                   let expr1', expr2' = (map_sym sym1, map_sym sym2) in
                   if eq then
                     annotate
                       ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
                       (Choreo.BinaryOp (expr1', expr2', Choreo.Eq))
                   else
                     annotate
                       ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
                       (Choreo.BinaryOp (expr1', expr2', Choreo.NotEq))
                 | CnfEq (sym, lit_val) ->
                   let expr' = map_sym sym in
                   let sym_expr' =
                     match lit_val with
                     | BoolLit bool_val ->
                       if bool_val then
                         annotate
                           ~ty:
                             (Some { t_expr = Choreo.BoolTy; is_const = true })
                           Choreo.True
                       else
                         annotate
                           ~ty:
                             (Some { t_expr = Choreo.BoolTy; is_const = true })
                           Choreo.False
                     | IntLit int_val ->
                       annotate
                         ~ty:(Some { t_expr = Choreo.IntTy; is_const = true })
                         (Choreo.IntLit int_val)
                     | StringLit str_val ->
                       annotate
                         ~ty:
                           (Some { t_expr = Choreo.StringTy; is_const = true })
                         (Choreo.StringLit str_val)
                   in
                   if eq then
                     annotate
                       ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
                       (Choreo.BinaryOp (expr', sym_expr', Choreo.Eq))
                   else
                     annotate
                       ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
                       (Choreo.BinaryOp (expr', sym_expr', Choreo.NotEq))
               in
               List.map
                 (List.map (function
                   | Positive x -> map_cnf_bool_constraint ~eq:true x
                   | Negative x -> map_cnf_bool_constraint ~eq:false x))
                 instantiation_constraints
             in
             (* TODO rewrite instantiation constraints converting @trigger and 
            bindings symbols alike back to computation expressions *)

             (* the (potentially more restricted) self to be propagated to 
             nested trigger scopes carries ALL implicit constraints *)
             let self =
               { self with
                 encoding =
                   List.sort_uniq
                     cnf_clause_compare
                     (cnf_and self.encoding implicit_bindings)
               }
             in
             { uid
             ; label
             ; marking
             ; event'
             ; self
             ; communication
             ; symbols
             ; implicit_bindings
             ; instantiation_constraints
             ; instantiation_constraint_exprs
             ; local_bindings
             ; data_expr'
             })
    in
    res
  (* *)
  and project_event (ctxt : ProjectionContext.t) (event' : event') =
    let derive_remote_participants (role_ctxts : RoleCtxt.t StringMap.t) :
        CnfUserset.t =
      let add_implicit_ (role_ctxt : RoleCtxt.t) =
        List.fold_left
          (fun encoding clause -> Sat.cnf_and encoding [ clause ])
          role_ctxt.role.encoding
          role_ctxt.implicit_constraints
      in
      List.fold_left
        (fun user_set (role_ctxt : RoleCtxt.t) ->
          let encoding = add_implicit_ role_ctxt in
          let cnf_role = { role_ctxt.role with encoding } in
          StringMap.add role_ctxt.role.label cnf_role user_set)
        CnfUserset.empty
        (StringMap.bindings role_ctxts |> List.map snd)
    in

    let trigger_ctxt = ctxt.ProjectionContext.trigger_ctxt in
    let self = TriggerCtxt.self trigger_ctxt in
    let abstract_self = ctxt.abstract_self in
    let event_id = (fst event'.data.info.data).data in

    (* debug *)
    (* print_endline
    @@ Printf.sprintf
         "\n\n\n    >>>> called with event_id=%s   self=%s\n\n"
         event_id
         (CnfRole.to_string self); *)
    let filter_out_abstract_self_marker (self_role : CnfRole.t) =
      (* print_endline
      @@ Printf.sprintf "before cleaning: %s" (CnfRole.to_string self_role); *)
      let encoding =
        List.filter
          (fun x ->
            x <> [ Positive (CnfEq ("@self", BoolLit true)) ]
            && x <> [ Negative (CnfEq ("@self", BoolLit true)) ])
          self_role.encoding
      in
      let self_role = { self_role with encoding } in
      (* print_endline
      @@ Printf.sprintf "after cleaning: %s" (CnfRole.to_string self_role); *)
      self_role
    in

    (* let add_self_marker (role : CnfRole.t) =
      let encoding =
        List.sort_uniq
          cnf_clause_compare
          (cnf_and
             role.encoding
             [ [ Positive (CnfEq ("@self", BoolLit true)) ] ])
      in
      { role with encoding }
    in *)

    (* Tx/Rx events explicitly exclude @self from the "remote"-side *)
    let exclude_abstract_self (roles : CnfUserset.t) : CnfUserset.t =
      CnfUserset.exclude_role roles abstract_self
    in

    let trigger_ctxt, communication_ctxt =
      CommunicationCtxt.of_communication_expr
        event_id
        event'.data.participants.data
        trigger_ctxt
    in
    let ctxt = { ctxt with trigger_ctxt } in

    (* debug *)
    (* print_endline @@ CommunicationCtxt.to_string communication_ctxt; *)
    let { local_bindings; init_ctxt; rcv_ctxt; _ } : CommunicationCtxt.t =
      communication_ctxt
    in

    let initrs, rcvrs =
      (derive_remote_participants init_ctxt, derive_remote_participants rcv_ctxt)
    in

    let resolve_unify_self (role : CnfRole.t) =
      (* print_endline
      @@ Printf.sprintf
           "@resolve_unify_self - self = %s"
           (CnfRole.to_string self);
      print_endline
      @@ Printf.sprintf
           "@resolve_unify_self - role = %s"
           (CnfRole.to_string role); *)
      Option.bind
        (CnfRole.resolve_role_intersection abstract_self role)
        (fun _ -> CnfRole.resolve_role_intersection self role)
    in

    let tx_opt, rx_opt =
      ( StringMap.find_opt self.label init_ctxt
      , StringMap.find_opt self.label rcv_ctxt )
      |> function
      | Some tx_ctxt, Some rx_ctxt ->
        (* debug *)
        (* print_endline
        @@ Printf.sprintf
             "\ntx_opt for role: %s"
             (CnfRole.to_string tx_ctxt.role);
        print_endline
        @@ Printf.sprintf
             "rx_opt for role: %s\n"
             (CnfRole.to_string rx_ctxt.role); *)
        let common_constraints =
          List.filter
            (fun c1 ->
              List.exists (fun c2 -> c1 = c2) rx_ctxt.implicit_constraints)
            tx_ctxt.implicit_constraints
        in
        let add_common_constraints (role_ctxt : RoleCtxt.t) =
          let encoding =
            List.sort_uniq
              cnf_clause_compare
              (role_ctxt.role.encoding @ common_constraints)
          in
          let role = { role_ctxt.role with encoding } in
          { role_ctxt with role }
        in
        (* debug *)
        (* print_endline
        @@ Printf.sprintf
             "\ntx_opt after extending with common implicit: %s"
             (CnfRole.to_string @@ (add_common_constraints tx_ctxt).role);
        print_endline
        @@ Printf.sprintf
             "rx_opt after extending with common implicit: %s\n"
             (CnfRole.to_string @@ (add_common_constraints rx_ctxt).role); *)

        ( Some (add_common_constraints tx_ctxt)
        , Some (add_common_constraints rx_ctxt) )
      | _ as other -> other
    in
    (* reminder: at this point, the encodings for tx_opt and rx_opt (when Some) 
       include the active bindings (the ones actually binding them together) *)

    match (tx_opt, rx_opt) with
    | Some tx_ctxt, Some rx_ctxt ->
      (* debug *)
      (* print_endline @@ Printf.sprintf "\nRole label present in both sides"; *)

      (* partitioning of implicit constraints across tx and rx according
          to whether they appear: on both sides, on tx-only, on rx-only
        *)
      let implicit_common, implicit_tx_only, implicit_rx_only =
        let tx, rx =
          ( List.sort_uniq Sat.cnf_clause_compare tx_ctxt.implicit_constraints
          , List.sort_uniq Sat.cnf_clause_compare rx_ctxt.implicit_constraints
          )
        in
        let dual, tx_o =
          List.partition (fun c1 -> List.exists (fun c2 -> c1 = c2) rx) tx
        and _, rx_o =
          List.partition (fun c1 -> List.exists (fun c2 -> c1 = c2) tx) rx
        in
        (dual, tx_o, rx_o)
      in

      (* debug *)
      (* print_endline
      @@ Printf.sprintf
           "\ncommon constraints: %s"
           (unparse_cnf_formula implicit_common);
      print_endline
      @@ Printf.sprintf
           "tx-only constraints: %s"
           (unparse_cnf_formula implicit_tx_only);
      print_endline
      @@ Printf.sprintf
           "rx-only constraints: %s\n"
           (unparse_cnf_formula implicit_rx_only); *)

      (* TODO [revise] does it ever apply to rx? *)
      (* indicates whether tx/rx roles reduce to a user under all implicit constraints *)
      (* let is_implicit_tx_user, is_implicit_rx_user =
        let is_implicit_user (role : CnfRole.t) unbound_constraints =
          (not @@ is_user role)
          && is_user
             @@ { role with
                  encoding = cnf_and role.encoding unbound_constraints
                }
        in
        ( is_implicit_user tx_ctxt.role implicit_tx_only
        , is_implicit_user rx_ctxt.role implicit_rx_only )
      in *)

      (* debug *)
      (* print_endline
      @@ Printf.sprintf "\nrx is implicit user: %b" is_implicit_rx_user;
      print_endline
      @@ Printf.sprintf "tx is implicit user: %b\n" is_implicit_tx_user; *)

      (* remote user-sets as seen by @self, according to its role *)
      let init_set, rcv_set =
        (* Tx => @self leads local bindings; Rx => @self leads local bindings *)
        let tx_lead_local_bindings, rx_lead_local_bindings =
          let mapper =
            StringMap.map (fun (x : RoleCtxt.binding_info) ->
                (x.renaming, x.local_bind_expr'))
          in
          (mapper tx_ctxt.defines, mapper rx_ctxt.uses)
        in

        (* debug *)
        (* print_endline "\ntx_lead_local_bindings";
          List.iter
            (fun (_, (_, z)) ->
              print_endline (Frontend.Unparser.unparse_expr z))
            (StringMap.bindings tx_lead_local_bindings);
          print_endline "\nrx_lead_local_bindings";
          List.iter
            (fun (_, (_, z)) ->
              print_endline (Frontend.Unparser.unparse_expr z))
            (StringMap.bindings rx_lead_local_bindings);
          print_newline (); *)

        (* rewrite remote user-set according to the bindings in scope *)
        let rewrite local_bindings user_set_exprs =
          List.map
            (rewrite_userset
               (StringMap.union
                  (fun _ _ y -> Some y)
                  (TriggerCtxt.bindings trigger_ctxt)
                  local_bindings
               |> StringMap.map (fun e -> snd e)))
            user_set_exprs
        in
        ( rewrite rx_lead_local_bindings communication_ctxt.initiators
        , rewrite tx_lead_local_bindings communication_ctxt.receivers )
      in

      let tx_only_res, rx_only_res =
        let single_direction_project ~(tx : bool) (l_ctxt : RoleCtxt.t)
            (r_ctxt : RoleCtxt.t) (r_user_set : CnfUserset.t)
            (r_user_set_exprs : Endpoint.user_set_expr' list) =
          let try_single_direction_project (l_role : CnfRole.t) =
            begin
              match resolve_unify_self l_role with
              | None -> []
              | Some (self : CnfRole.t) ->
                let projection_type =
                  if tx then
                    TxO
                      ( l_ctxt.implicit_constraints
                      , CnfUserset.exclude_role r_user_set abstract_self
                      , r_user_set_exprs )
                  else
                    RxO
                      ( l_ctxt.implicit_constraints
                      , CnfUserset.exclude_role r_user_set abstract_self
                      , r_user_set_exprs )
                in
                project ctxt event' ~self ~projection_type ~local_bindings
            end
          in
          Option.fold
            (CnfRole.resolve_role_intersection l_ctxt.role r_ctxt.role)
            ~none:(try_single_direction_project l_ctxt.role)
            ~some:(fun _ ->
              let l_role = filter_out_abstract_self_marker l_ctxt.role
              and r_role = filter_out_abstract_self_marker r_ctxt.role in
              (* *)
              if is_user l_role then
                if is_user r_role then begin
                  (* two users and there is a potential intersection - the 
                  instantiation constraint should prevent full unification (msg from
                  @self to @self makes no sense). Maybe Babel should also flag and
                   prevent this at @runtime when values are known (?) *)
                  match CnfRole.resolve_role_diff l_role r_role with
                  | None ->
                    (* TODO ensure this is handled upstream (@ Projectability) *)
                    assert false
                  | Some lx_only_role ->
                    try_single_direction_project lx_only_role
                end
                else
                  (* user on lhs-only means the user is a member of the rhs-group *)
                  try_single_direction_project l_role
              else begin
                match CnfRole.resolve_role_diff l_role r_role with
                | None ->
                  (* tx-group contained in rx_role - will be caught by a dual instead *)
                  []
                | Some lx_only_role -> try_single_direction_project lx_only_role
              end)
        in
        (* let tx_only_res = *)
        ( single_direction_project ~tx:true tx_ctxt rx_ctxt rcvrs rcv_set
        , (* and rx_only_res = *)
          single_direction_project ~tx:false rx_ctxt tx_ctxt initrs init_set )
      (* *)
      (* let tx_only_res =
        let try_tx_only_project (tx_only_role : CnfRole.t) =
          begin
            match resolve_unify_self tx_only_role with
            | None -> []
            | Some (self : CnfRole.t) ->
              let projection_type =
                TxO
                  ( tx_ctxt.implicit_constraints
                  , CnfUserset.exclude_role rcvrs abstract_self
                  , rcv_set )
              in
              project ctxt event' ~self ~projection_type ~local_bindings
          end
        in
        Option.fold
          (CnfRole.resolve_role_intersection tx_ctxt.role rx_ctxt.role)
          ~none:(try_tx_only_project tx_ctxt.role)
          ~some:(fun _ ->
            let tx_role = filter_out_abstract_self_marker tx_ctxt.role
            and rx_role = filter_out_abstract_self_marker rx_ctxt.role in
            (* *)
            if is_user tx_role then
              if is_user rx_role then begin
                (* two users and there is a potential intersection - the 
            instantiation constraint should prevent full unification - msg from
            @self to @self makes no sense - maybe this is something that Babel
            should flag and prevent at @runtime? *)
                match CnfRole.resolve_role_diff tx_role rx_role with
                | None ->
                  (* TODO ensure this is handled upstream (@ Projectability) *)
                  assert false
                | Some tx_only_role -> try_tx_only_project tx_only_role
              end
              else
                (* user on lhs-only means the user is a member of the rhs-group *)
                try_tx_only_project tx_role
            else begin
              match CnfRole.resolve_role_diff tx_role rx_role with
              | None ->
                (* tx-group contained in rx_role - will be caught by a dual instead *)
                []
              | Some tx_only_role -> try_tx_only_project tx_only_role
            end) *)
      (* *)
      (* and rx_only_res =
        let project_rx_self rx_only_role =
          Option.fold
            (resolve_unify_self rx_only_role)
            ~none:[]
            ~some:(fun (self : CnfRole.t) ->
              let projection_type =
                let initrs =
                  if is_user rx_only_role then
                    CnfUserset.exclude_role
                      initrs
                      (filter_out_abstract_self_marker self)
                    (* CnfUserset.exclude_role initrs self *)
                  else initrs
                in
                RxO
                  ( rx_ctxt.implicit_constraints
                  , exclude_abstract_self initrs
                  , init_set )
              in
              project ctxt event' ~self ~projection_type ~local_bindings)
        in
        Option.fold
          (CnfRole.resolve_role_diff rx_ctxt.role tx_ctxt.role)
          ~none:
            (if is_user rx_ctxt.role then project_rx_self rx_ctxt.role else [])
          ~some:(fun diff_role -> project_rx_self diff_role) *)
      (*  *)
      (*  *)
      and tx_rx_res =
        Option.fold
          (CnfRole.resolve_role_intersection tx_ctxt.role rx_ctxt.role)
          ~none:[]
          ~some:(fun tx_rx_role ->
            if is_user tx_rx_role then
              (* already covered by tx_only and rx_only cases *)
              []
            else
              (* print_endline
              @@ Printf.sprintf
                   "tx_rx dual is a group: %s"
                   (CnfRole.to_string tx_rx_role); *)
              Option.fold
                (resolve_unify_self tx_ctxt.role)
                ~none:[]
                ~some:(fun (tx_rx_self_role : CnfRole.t) ->
                  (* TODO [revise] does it ever apply to rx? *)
                  (* indicate whether tx/rx roles reduce to a user under all implicit constraints *)
                  let is_implicit_tx_user =
                    let tx_role =
                      { tx_rx_role with
                        encoding =
                          List.sort_uniq
                            cnf_clause_compare
                            (cnf_and tx_rx_role.encoding implicit_tx_only)
                      }
                    in
                    (not @@ is_user tx_rx_role) && (is_user @@ tx_role)
                  and is_implicit_rx_user =
                    let role =
                      { tx_rx_role with
                        encoding =
                          List.sort_uniq
                            cnf_clause_compare
                            (cnf_and tx_rx_role.encoding implicit_rx_only)
                      }
                    in
                    (not @@ is_user tx_rx_role) && (is_user @@ role)
                  in

                  (* debug *)
                  (* print_endline
                    @@ Printf.sprintf
                         "\nrx is implicit user: %b"
                         is_implicit_rx_user;
                    print_endline
                    @@ Printf.sprintf
                         "tx is implicit user: %b\n"
                         is_implicit_tx_user; *)
                  let tx_implicit_constraints =
                    let tx_encoding =
                      cnf_and tx_ctxt.role.encoding tx_ctxt.implicit_constraints
                    in
                    if is_implicit_rx_user then
                      List.concat_map (fun x -> [ x ]) implicit_rx_only
                      |> cnf_neg |> cnf_and tx_encoding
                    else tx_encoding |> List.sort_uniq cnf_clause_compare
                  and rx_implicit_constraints =
                    let rx_encoding =
                      cnf_and rx_ctxt.role.encoding rx_ctxt.implicit_constraints
                    in
                    if is_implicit_tx_user then
                      List.concat_map (fun x -> [ x ]) implicit_tx_only
                      |> cnf_neg |> cnf_and rx_encoding
                    else rx_encoding |> List.sort_uniq cnf_clause_compare
                  in

                  (* debug *)
                  (* print_endline
                    @@ Printf.sprintf
                         "\nself_tx_ctxt.tx_implicit_constraints: %s"
                         (unparse_cnf_formula tx_ctxt.implicit_constraints);
                    print_endline
                    @@ Printf.sprintf
                         "tx_implicit_constraints: %s"
                         (unparse_cnf_formula tx_implicit_constraints);
                    print_endline
                    @@ Printf.sprintf
                         "self_rx_ctxt.rx_implicit_constraints: %s"
                         (unparse_cnf_formula rx_ctxt.implicit_constraints);
                    print_endline
                    @@ Printf.sprintf
                         "rx_implicit_constraints: %s\n"
                         (unparse_cnf_formula rx_implicit_constraints); *)
                  (* let self =
                      { self with
                        encoding =
                          List.sort_uniq
                            cnf_clause_compare
                            (cnf_and self.encoding tx_rx_self_role.encoding)
                      }
                    in *)
                  let self =
                    { self with
                      encoding =
                        Option.get
                        @@ Sat.cnf_sat_solve
                             (cnf_and self.encoding tx_rx_self_role.encoding)
                    }
                  in
                  (* print_endline
                    @@ Printf.sprintf
                         "adjusted self %s"
                         (CnfRole.to_string self); *)

                  (* List.iter
                      (fun x ->
                        print_endline
                        @@ Printf.sprintf
                             "+++++++++++ rewriten rcv_set: %s"
                             (Frontend.Unparser.unparse_user_set_expr x))
                      (deannotate_list communication_ctxt.rcv_set); *)

                  (* let init_set, rcv_set =
                      let derive_set local_bindings user_set_exprs =
                        List.map
                          (rewrite_userset
                             (StringMap.union
                                (fun _ _ y -> Some y)
                                (TriggerCtxt.bindings trigger_ctxt)
                                local_bindings
                             |> StringMap.map (fun e -> snd e)))
                          user_set_exprs
                      in
                      ( derive_set
                          rx_lead_local_bindings
                          communication_ctxt.init_set
                      , derive_set
                          tx_lead_local_bindings
                          communication_ctxt.rcv_set )
                    in *)

                  (* in
                    let init_set =
                      List.map
                        (rewrite_userset
                           (StringMap.union
                              (fun _ _ y -> Some y)
                              (TriggerCtxt.bindings trigger_ctxt)
                              rx_lead_local_bindings
                           |> StringMap.map (fun e -> snd e)))
                        communication_ctxt.init_set
                    and rcv_set =
                      List.map
                        (rewrite_userset
                           (StringMap.union
                              (fun _ _ x -> Some x)
                              (TriggerCtxt.bindings trigger_ctxt)
                              tx_lead_local_bindings
                           |> StringMap.map (fun e -> snd e)))
                        communication_ctxt.rcv_set
                    in *)

                  (* List.iter
                      (fun x ->
                        print_endline
                        @@ Printf.sprintf
                             "+++++++++++ rewriten rcv_set: %s"
                             (Frontend.Unparser.unparse_user_set_expr x))
                      (deannotate_list rcv_set); *)
                  (* List.iter
                      (fun x ->
                        print_endline
                        @@ Printf.sprintf
                             "+++++++++++ rewriten rcv_set: %s"
                             (Frontend.Unparser.unparse_user_set_expr x))
                      (deannotate_list init_set); *)

                  let projection_type =
                    TxRx
                      ( ( tx_implicit_constraints
                        , exclude_abstract_self rcvrs
                        , rcv_set )
                      , ( rx_implicit_constraints
                        , exclude_abstract_self initrs
                        , init_set ) )
                  in

                  let local_bindings =
                    let nested_bindings =
                      StringMap.map
                        (fun (x : RoleCtxt.binding_info) ->
                          (x.renaming, x.spawn_bind_expr'))
                        tx_ctxt.defines
                    in
                    StringMap.union
                      (fun _ _ y -> Some y)
                      (TriggerCtxt.bindings trigger_ctxt)
                      nested_bindings
                  in

                  project ctxt event' ~self ~projection_type ~local_bindings))
      in

      let projections = tx_only_res @ tx_rx_res @ rx_only_res in

      ProjectionContext.include_projected_event event_id projections ctxt
    | Some tx_ctxt, None ->
      let rcv_set =
        List.map
          (rewrite_userset
             (TriggerCtxt.bindings trigger_ctxt
             |> StringMap.map (fun e -> snd e)))
          communication_ctxt.receivers
      in
      let self =
        { self with
          encoding =
            Option.get
            @@ Sat.cnf_sat_solve (cnf_and self.encoding tx_ctxt.role.encoding)
        }
      in
      let projection_type =
        if StringMap.is_empty rcv_ctxt then Local tx_ctxt.implicit_constraints
        else TxO (tx_ctxt.implicit_constraints, rcvrs, rcv_set)
      in
      let projections =
        project ctxt event' ~self ~local_bindings ~projection_type
      in
      ProjectionContext.include_projected_event event_id projections ctxt
    | None, Some rx_ctxt ->
      let init_set =
        List.map
          (rewrite_userset
             (TriggerCtxt.bindings trigger_ctxt
             |> StringMap.map (fun e -> snd e)))
          communication_ctxt.initiators
      in
      let self =
        { self with
          encoding =
            Option.get
            @@ Sat.cnf_sat_solve (cnf_and self.encoding rx_ctxt.role.encoding)
        }
      in
      let projection_type =
        RxO (rx_ctxt.implicit_constraints, initrs, init_set)
      in
      let rx_event =
        project ctxt event' ~self ~projection_type ~local_bindings
      in
      ProjectionContext.include_projected_event event_id rx_event ctxt
    | None, None -> ctxt
    (* in
    { ctxt_res with trigger_ctxt } *)
  in
  List.fold_left project_event ctxt events

and project_relations (ctxt : ProjectionContext.t)
    (relations : Choreo.relation' list) =
  let rec project_spawn_relation (ctxt : ProjectionContext.t)
      (relation' : Choreo.relation') : ProjectionContext.t =
    let uid = Option.get !(relation'.uid) in
    match relation'.data with
    | Choreo.ControlRelation _ ->
      (* delay ctrl-flow relations until all spawn relations are projected, and
         on the recursion's way up *)
      ctxt
    | Choreo.SpawnRelation (src_id', trigger_id, _expr', spawn_program) -> begin
      (* TODO include guard in relations *)
      let src = Env.find_flat_opt src_id'.data ctxt.projected_events_env in
      (* reminder: depending on the role, we might not have a projection for
         the event *)
      (* fold_left_error
           (fun ((ctxt, { events; relations }) :
                  ProjectionContext.t * Projection.projection)
                (event : Projection.event) ->
             let ctxt = ProjectionContext.begin_scope event ctxt in
             project_spawn_program ctxt spawn_program >>= fun ctxt ->
             let projection = ProjectionContext.projection ctxt in
             let ctxt = ProjectionContext.end_scope ctxt in
             let events = projection.events @ events
             and relations = projection.relations @ relations in
             let (projection : Projection.projection) = { events; relations } in
             Ok (ctxt, projection))
           (ctxt, { events = []; relations = [] })
           (Option.fold ~none:[] ~some:Fun.id src)
         >>= fun (ctxt, projection) ->
         match projection with
         | { events = []; relations = [] } -> Ok ctxt
         | _ ->
           let (spawn_relation : Projection.relation) =
             SpawnRelation (uid, src_id'.data, projection)
           in
           let ctxt = ProjectionContext.add_relation ctxt spawn_relation in
           Ok ctxt) *)
      (* This alternative could seem reduntant since we already have constraints attached
         to events (no point in attaching guards to spawns for the same purpose);
         nonetheless, it's required for duals *)
      List.fold_left
        (fun (ctxt : ProjectionContext.t) (event : Projection.event_t) ->
          let ctxt = ProjectionContext.begin_scope trigger_id event ctxt in
          project_spawn_program ctxt spawn_program
          |> fun (ctxt : ProjectionContext.t) ->
          let projection = List.hd ctxt.projection in
          let src_uid = event.uid in
          let instantiation_constraints =
            event.instantiation_constraint_exprs
          in
          (* TODO extract method for relation renaming for subgraphs (needed in Babel) *)
          let (spawn_relation : Projection.relation) =
            ( instantiation_constraints
            , SpawnRelation
                ( trigger_id
                , src_uid ^ "_" ^ uid
                , (src_uid, src_id'.data)
                , projection ) )
          in
          let ctxt = ProjectionContext.end_scope ctxt in
          let ctxt = ProjectionContext.add_relation ctxt spawn_relation in
          ctxt)
        ctxt
        (Option.fold ~none:[] ~some:Fun.id src)
    end
  in
  let project_fst_degree_cf_rel (ctxt, acc) (relation' : Choreo.relation') :
      ProjectionContext.t * Projection.relation list =
    let uid = Option.get !(relation'.uid) in
    match relation'.data with
    | Choreo.ControlRelation (src_id', _, target_id', rel_type') ->
      let srcs_opt = ProjectionContext.projections_find_opt src_id'.data ctxt
      and targets_opt =
        ProjectionContext.projections_find_opt target_id'.data ctxt
      in
      begin
        match (srcs_opt, targets_opt) with
        | Some srcs, Some targets ->
          (* sort out (src,target,self) tuples, where self is the non-empty
             intersection of src.self and target.self, which will act as the
             constraint deciding the instantiation of the relation *)
          let candidates =
            list_combine
              (fun (e1 : Projection.event_t) (e2 : Projection.event_t) ->
                Option.bind
                  (cnf_sat_solve
                  @@ cnf_and
                       e1.instantiation_constraints
                       e2.instantiation_constraints)
                  (fun constraints -> Some (e1, e2, constraints)))
                (* Option.bind
                  (CnfRole.resolve_role_intersection e1.self e2.self)
                  (fun self -> Some (e1, e2, self))) *)
              srcs
              targets
            |> List.filter_map Fun.id
          in
          (* partition flow-control relations:
             {Local|Tx --> Local|Tx]} + {Rx -> Local|Tx} + {? -> Rx }
          *)
          let init_init, rx_init, x_rcv =
            List.partition
              (fun (_, (e2 : Projection.event_t), _) ->
                match e2.communication with
                | Local | Tx _ | TxO _ -> true
                | Rx _ | RxO _ -> false)
              candidates
            |> fun (x_init, x_rcv) ->
            let init_init, rx_init =
              List.partition
                (fun ((e1 : Projection.event_t), _, _) ->
                  match e1.communication with
                  | Local | Tx _ | TxO _ -> true
                  | Rx _ | RxO _ -> false)
                x_init
            in
            (init_init, rx_init, x_rcv)
          in
          (* project all {? -> Local|T} relations now - these are straightfoward
           direct dependencies *)
          let ctxt, _ =
            List.fold_left_map
              (fun ctxt
                   ( (e1 : Projection.event_t)
                   , (e2 : Projection.event_t)
                   , constraints )
                 ->
                (* !!!TODO resolve intersection as expr'-based constraint *)
                let rel =
                  (* ( ([] : expr' list list) *)
                  ( to_instantiation_constraint_exprs
                      constraints
                      ctxt.ProjectionContext.trigger_ctxt
                  , Projection.ControlFlowRelation
                      ( uid
                      , (e1.uid, (fst e1.event'.data.info.data).data)
                      , (e2.uid, (fst e2.event'.data.info.data).data)
                      , rel_type'.data
                      , constraints ) )
                  (* , self ) ) *)
                in
                (ProjectionContext.add_relation ctxt rel, rel))
              ctxt
              (init_init @ rx_init)
          in
          (* make {Rx -> Local|T} relations visible to nested scopes - required 
          to decide on "2nd degree" dependencies *)
          let ctxt, _ =
            List.fold_left_map
              (fun ctxt
                   ((e1 : Projection.event_t), (e2 : Projection.event_t), self)
                 ->
                let src_uid = e1.uid
                and target_info =
                  (e2.uid, (fst e2.event'.data.info.data).data)
                in
                let target_info = (target_info, rel_type'.data, self) in
                ( ProjectionContext.add_rx_sourced_relation
                    ctxt
                    src_uid
                    target_info
                , target_info ))
              ctxt
              rx_init
          in
          (* delay analysis of {? -> Rx } relations until after the recursion
             bottoms out (i.e., all spawn relations projected) *)
          let acc =
            List.fold_left
              (fun acc
                   ( (e1 : Projection.event_t)
                   , (e2 : Projection.event_t)
                   , constraints )
                 ->
                let rel =
                  (* ( ([] : expr' list list) *)
                  ( to_instantiation_constraint_exprs
                      constraints
                      ctxt.ProjectionContext.trigger_ctxt
                  , Projection.ControlFlowRelation
                      ( uid
                      , (e1.uid, (fst e1.event'.data.info.data).data)
                      , (e2.uid, (fst e2.event'.data.info.data).data)
                      , rel_type'.data
                      , constraints ) )
                in
                rel :: acc)
              []
              x_rcv
            @ acc
          in
          (ctxt, acc)
        | _ ->
          (* unless we have something projected at each end of the relation,
             the relation does not get a projection *)
          (ctxt, acc)
      end
    | Choreo.SpawnRelation _ ->
      (* resolved on the recursion's way down *)
      (ctxt, acc)
  (* TODO must further intersect self to ensure proper matching across scopes - use unions *)
  and project_snd_degree_cf_rel (ctxt : ProjectionContext.t)
      (relation : Projection.relation) : ProjectionContext.t =
    (* !!!!TODO handle expr'-based constraint *)
    match relation with
    | ( _
      , Projection.ControlFlowRelation (_, _, (target_uid, _), rel_type_1, _self)
      ) ->
      (* decide which {? -> Rx } relations should project (if any) - at this
         point we have all the information available *)
      let rx_x =
        Option.fold
          ~none:[]
          ~some:Fun.id
          (ProjectionContext.rx_sourced_with_uid_find_opt ctxt target_uid)
      in
      let ctxt =
        List.fold_left
          (fun ctxt (_, rel_type_2, _) ->
            match (rel_type_1, rel_type_2) with
            | Include, Milestone
            | Exclude, Milestone
            | Response, Milestone
            | Include, Condition
            | Exclude, Condition -> ProjectionContext.add_relation ctxt relation
            | _ -> ctxt)
          ctxt
          rx_x
      in
      ctxt
    (* !!!!TODO handle expr'-based constraint *)
    | _, Projection.SpawnRelation _ ->
      (* already handled on the recursion's way down *)
      ctxt
  in
  List.fold_left project_fst_degree_cf_rel (ctxt, []) relations
  |> fun (ctxt, delayed_ctrl_flows) ->
  List.fold_left project_spawn_relation ctxt relations |> fun ctxt ->
  List.fold_left project_snd_degree_cf_rel ctxt delayed_ctrl_flows

and fold_role_cnf ~none ~some = function
  | None -> none
  | Some (label, (params, cnf)) -> Some (label, (params, some cnf))

and fold_role ?(none = None) ~some = function
  | None -> none
  | Some role -> some role

and to_endpoint (ctxt : ProjectionContext.t)
    ({ events; relations } : Projection.program) : Endpoint.endpoint =
  let events = List.map (to_endpoint_event ctxt) events
  and relations = List.map (to_endpoint_relation ctxt) relations
  and role_decl = ctxt.ProjectionContext.role_decl'.data in
  { role_decl; events; relations }

and to_endpoint_event (ctxt : ProjectionContext.t)
    ({ event'
     ; uid
     ; label
     ; marking
     ; data_expr'
     ; instantiation_constraint_exprs
     ; communication
     ; _
     } as event_t :
      Projection.event_t) : Endpoint.event =
  (* TODO [revisit] replacing with newly-generated uid (duals) - is this ok?  *)
  let element_uid = Option.get !(event'.uid) in
  let id = (fst event'.data.info.data).data in
  let (bool_ty : Choreo.type_info option) =
    Some { t_expr = BoolTy; is_const = false }
  in
  (* refactor *)
  let instantiation_constraint_opt =
    let rec fold op lst =
      let rec fold_helper acc = function
        | [] -> acc
        | x :: xs ->
          fold_helper (annotate ~ty:bool_ty (Choreo.BinaryOp (x, acc, op))) xs
      in
      fold_helper (List.hd lst) (List.tl lst)
    in
    if List.is_empty instantiation_constraint_exprs then None
    else
      List.map (fun x -> fold Choreo.Or x) instantiation_constraint_exprs
      |> fun x -> fold Choreo.And x |> Option.some
  and ifc_constraint_opt =
    (* let uid = (snd event_t.event'.data.info.data).data in *)
    (* print_endline @@ "Uid: " ^ element_uid;
    print_endline ""; *)
    Option.fold
      (StringMap.find_opt element_uid ctxt.ProjectionContext.ifc_constraints_by_uid)
      ~none:None
      ~some:(fun ifc ->
        match communication with
        | Local | Tx _ | TxO _ -> Some ifc
        | _ -> None)
  (* TODO [cleanup renaming using consts here] *)
  and id, communication =
    match communication with
    | Local -> (id, Endpoint.Local)
    | Tx (_, receivers) -> (id, Endpoint.Tx receivers)
    | TxO (_, receivers) -> (id, Endpoint.Tx receivers)
    | Rx (_, initiators) -> (id, Endpoint.Rx initiators)
    | RxO (_, initiators) -> (id, Endpoint.Rx initiators)
  in
  { element_uid
  ; uid
  ; id
  ; label
  ; data_expr'
  ; marking
  ; instantiation_constraint_opt
  ; ifc_constraint_opt
  ; communication
  }

and to_endpoint_relation (ctxt : ProjectionContext.t)
    (relation : Projection.relation) : Endpoint.relation =
  let to_constraint instantiation_constraint_exprs =
    let (bool_ty : Choreo.type_info option) =
      Some { t_expr = BoolTy; is_const = false }
    in
    let rec fold op lst =
      let rec fold_helper acc = function
        | [] -> acc
        | x :: xs ->
          fold_helper (annotate ~ty:bool_ty (Choreo.BinaryOp (x, acc, op))) xs
      in
      fold_helper (List.hd lst) (List.tl lst)
    in
    if List.is_empty instantiation_constraint_exprs then None
    else
      List.map (fun x -> fold Choreo.Or x) instantiation_constraint_exprs
      |> fun x -> fold Choreo.And x |> Option.some
  in
  match relation with
  | constrnt, ControlFlowRelation (uid, src, target, rel_type, _e) ->
    let (relation_type : Endpoint.relation_t) =
      Endpoint.ControlFlowRelation { target; rel_type }
    and instantiation_constraint_opt = to_constraint constrnt
    and guard_opt = None in
    { uid; src; guard_opt; relation_type; instantiation_constraint_opt }
  | constrnt, SpawnRelation (trigger_id, uid, src, graph) ->
    let instantiation_constraint_opt = to_constraint constrnt in
    let graph = to_endpoint ctxt graph in
    let (relation_type : Endpoint.relation_t) =
      Endpoint.SpawnRelation { graph; trigger_id }
    and guard_opt = None in
    { uid; src; guard_opt; relation_type; instantiation_constraint_opt }

let rec project (program : Choreo.program)
    (ifc_constraints_by_uid : expr' StringMap.t) : Endpoint.endpoint list =
  let project_role ctxts ctxt =
    project_spawn_program ctxt program.spawn_program |> fun ctxt ->
    tmp_debug ctxt;
    ctxt :: ctxts
  and init_ctxts =
    List.map (ProjectionContext.init ifc_constraints_by_uid) program.roles
  in
  StringMap.iter ( fun x y -> print_endline @@ x ^": " ^Frontend.Unparser.unparse_expr y) ifc_constraints_by_uid;
  print_endline @@ " End.......";
    List.fold_left project_role [] init_ctxts
  (* (bad acces to stack-like structure)
    TODO cleanup/refactoring - hide this - encapsulate within ProjectionContext *)
  |> List.map (fun ctxt ->
         (* ( ctxt.ProjectionContext.abstract_self.label,*)
         to_endpoint ctxt (List.hd ctxt.ProjectionContext.projection))

(* TODO remove tmp debug *)
(* DEBUGS (tmp) *)
and tmp_debug (ctxt : ProjectionContext.t) =
  print_endline
  @@ Printf.sprintf
       "\n\n\
        Debug @ projection.ml\n\
        Projection for %s\n\
        ==========================\n\
       \ \n\
        %s\n\n\
        ==========================\n"
       (ProjectionContext.self ctxt).label
       (Projection.unparse_projection (ProjectionContext.projection ctxt))
