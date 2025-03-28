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

type projection_t =
  | Local
  | TxO of CnfUserset.t
  | RxO of CnfUserset.t
  | TxRx of CnfUserset.t * CnfUserset.t

module Symbols : sig
  val next_trigger_val_sym : unit -> event_id

  val encodes_trigger_val_sym : string -> bool

  val next_param_val_sym : unit -> event_id

  val next_bind_sym : unit -> string

  val encode_param_name : event_id -> event_id

  val encodes_param_name : event_id -> bool
end = struct
  let trigger_sym_val_prefix = "@V"

  let param_sym_val_prefix = "@P"

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

  and next_param_val_sym () =
    Printf.sprintf "%s%d" param_sym_val_prefix @@ next_int ()

  and next_bind_sym () =
    Printf.sprintf "%s%d" param_bind_sym_prefix @@ next_int ()

  and encode_param_name identifier =
    Printf.sprintf "%s%s" param_name_prefix identifier

  and encodes_param_name identifier =
    String.starts_with ~prefix:param_sym_val_prefix identifier
end

module TriggerCtxt : sig
  type t

  val init : self:CnfRole.t -> t
end = struct
  exception Internal_error of string

  type t = (event_id * scope) list

  and scope =
    { self : CnfRole.t
    ; trigger_symbols : string StringMap.t
    ; bindings : string StringMap.t
    }

  let rec bootstrap_initiator : CnfRole.t =
    { label = "#ROOT"; param_types = StringMap.empty; encoding = [] }

  and bootstrap_event_id = "#bootstrap"

  and init ~(self : CnfRole.t) =
    let trigger_symbols = StringMap.empty
    and bindings = StringMap.empty in
    [ (bootstrap_event_id, { self; trigger_symbols; bindings }) ]

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
      ~none:
        (let sym = Symbols.next_trigger_val_sym () in
         let id, ({ trigger_symbols; _ } as scope) = peek t in
         let trigger_symbols = StringMap.add trigger_key sym trigger_symbols in
         let t = update_top (fun _ -> (id, { scope with trigger_symbols })) t in
         (t, sym))
      ~some:(fun sym -> (t, sym))
      (StringMap.find_opt trigger_key (snd (peek t)).trigger_symbols)
end

(** [list_combine f [a1; ...; an] [b1; ...; bm]] returns the list
    [[f a1 b1; f a1 b2; ...; f an bm]], resulting from applying function [f] to
    each element in the cartesian product of [[a1; ...; an]] and
    [[b1; ...; bm]]. *)
let list_combine : 'a 'b 'c. ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list =
 fun combinator l1 l2 ->
  List.concat (List.map (fun l1 -> List.map (fun l2 -> combinator l1 l2) l2) l1)

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
end

(* TODO move somewhere else *)
module Projection = struct
  open Choreo

  type program =
    { events : event list
    ; relations : relation list
    }

  and event =
    { event' : Choreo.event'
    ; uid : identifier
    ; self : CnfRole.t
    ; communication : communication
    ; symbols : expr' StringMap.t
    }

  and relation =
    | ControlFlowRelation of
        element_uid
        * (element_uid * event_id)
        * (element_uid * event_id)
        * relation_type
        * CnfRole.t
    | SpawnRelation of element_uid * (element_uid * event_id) * program

  and communication =
    | Local
    | Tx of CnfUserset.t
    | Rx of CnfUserset.t

  let rec unparse_events ?(indent = "") (events : event list) =
    let rec unparse_event (e : event) =
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

  and unparse_projection ?(indent = "") ({ events; relations } : program) =
    let unparsed_events = unparse_events ~indent events
    and unparsed_relations = unparse_relations ~indent relations in
    if unparsed_relations = "" then unparsed_events
    else
      Printf.sprintf "%s\n%s;\n\n%s" unparsed_events indent unparsed_relations
end

(* Indicates whether a constrained role encodes a single user.

   Observation: a user has every role parameter constrained to either
   a value (e.g., [#p1=2]) or a "trigger" symbol (e.g., [#p1=@V3], and
   @V3=@trigger.value). Runtime aliases (e.g., '#p1 as X') can
   introduce constraints of the form [#p1 = #p2]) but these carry different
   semantics ("shape constraints").
*)
let rec is_user (role : CnfRole.t) =
  let params, cnf = (role.param_types, role.encoding) in
  List.fold_left
    (fun acc param ->
      let param_sym = Symbols.encode_param_name param in
      acc
      && List.exists
           (function
             | [ Positive (CnfSymEq (s1, s2)) ] ->
               (s1 = param_sym && Symbols.encodes_trigger_val_sym s2)
               || (Symbols.encodes_trigger_val_sym s1 && s2 = param_sym)
             | [ Positive (CnfEq (s, _)) ] -> param_sym = s
             | _ -> false)
           cnf)
    true
    (StringMap.bindings params |> List.map fst)

module ProjectionContext = struct
  (*
  _____________
  abstract_self : symbolic representation of the runtime participant;
  > e.g., P(p1=@s0; p2=@s1), with @s0=@self.value.p1, @s1=@self.value.p2
  ____
  self : the role for which we are projecting
  __________
  projection
  __________
  a stack-like structure to build a projection as scopes are traversed
  _______
  counter
  =======
  incremented to generate fresh symbols
  ___________________
  symbols_by_elem_uid
  ===================
  binds event uids to the trigger-driven symbols introduced by their userset
  exprs - with each spawn, the triggering event adds its symbols to the 
  top-level context
  ___________
  trigger_chain
  ===========
  keeps track of the trigger chain in order to sort out Inititator/Receiver
  expressions (event_id)
  _____________________________
  symbols_by_trigger_string_env
  =============================
  environment binding stringified @trigger exprs to fresh symbols
  (e.g., "@trigger.value.cid" -> "@V3" )
  ______________________
  trigger_expr_by_symbol
  ======================
  mapping associating @trigger-based symbols to actual exprs
  (e.g. "@V3" ->  @trigger.value.cid ) - computation expressions
  to eval'd and linked to specific symbols at runtime, (and which
  only make sense at that point), in order to blindy evaluate
  (cnf) constraints
  _____________________________
  control_flow_candidates_stack
  =============================
  stacks the control-flow relations of each scope on the recursion's way "down",
  delaying its processing to when the recursion bottoms
  *)

  (* TODO [refactoring/tentative] partition context.t into envs, stacks and globals *)
  type t =
    { abstract_self : CnfRole.t
    ; trigger_ctxt : TriggerCtxt.t
    ; self : CnfRole.t list
    ; projection : Projection.program list
    ; counter : int ref
    ; symbols_by_elem_uid : StringSet.t StringMap.t
    ; trigger_chain : (event_id * Projection.event) list
    ; symbols_by_trigger_string_env : identifier Env.t
    ; trigger_expr_by_symbol : expr' StringMap.t
    ; projected_events_env : Projection.event list Env.t
    ; sourcing_rx_relations_by_uid :
        ((element_uid * event_id) * relation_type * CnfRole.t) list StringMap.t
          (* TODO deprecate *)
    ; control_flow_candidates_stack : Projection.relation list list
    }

  (* and direct_dep_t = (event_id * element_uid) * (event_id * element_uid) *)

  let mk_abstract_self (self : CnfRole.t) : CnfRole.t =
    let label, param_types = (self.label, self.param_types) in
    let _, encoding =
      List.fold_left
        (fun (counter, cnf) (param_label, _) ->
          (* let param_label_sym = Printf.sprintf "%s#%s" label param_label in *)
          let param_label_sym = Printf.sprintf "#%s" param_label in
          let param_value_sym = Printf.sprintf "@s%d" counter in
          ( counter + 1
          , [ Positive (CnfSymEq (param_label_sym, param_value_sym)) ] :: cnf ))
        (0, [])
        (StringMap.bindings param_types)
    in
    { label; param_types; encoding }
  (* (label, (params, cnf)) *)

  let init (self : CnfRole.t) =
    (* maps each role parameter to a regular computation expression whose
       .eval() is expected to return the parameter's value at runtime
       e.g., @self.value.cid
    *)
    let rec wrap_self_as_prop_derefs () : (identifier * expr') list =
      let to_type_info type_expr =
        Some { t_expr = type_expr; is_const = true }
      in
      (* let label, param_types = self.label, self.param_types in *)
      (* let param_types = self.param_types in *)
      let record_ty_info =
        List.map
          (fun (param_name, param_ty) ->
            let named_param' = annotate param_name
            and type_info_opt = to_type_info param_ty in
            let type_expr' = annotate ~ty:type_info_opt param_ty in
            annotate ~ty:type_info_opt (named_param', type_expr'))
          (StringMap.bindings self.param_types)
        |> fun record_field_tys -> to_type_info (RecordTy record_field_tys)
      in
      let self_id' = annotate "@self"
      and value_id' = annotate "value"
      and self_ref_ty = to_type_info (EventRefTy ("@self", true)) in
      let self_ref_expr = annotate ~ty:self_ref_ty (EventRef self_id') in
      let val_deref_expr =
        annotate ~ty:record_ty_info (PropDeref (self_ref_expr, value_id'))
      in
      List.map
        (fun ((param_label, param_type) : string * type_expr) ->
          let param_id = Printf.sprintf "%s" param_label in
          let param_id' = annotate param_id in
          (* let param_id_key = Printf.sprintf "%s#%s" role_label param_label in *)
          let param_id_key = Printf.sprintf "#%s" param_label in
          let param_deref_ty = to_type_info param_type in
          let param_deref_expr =
            annotate ~ty:param_deref_ty (PropDeref (val_deref_expr, param_id'))
          in
          (param_id_key, param_deref_expr))
        (StringMap.bindings self.param_types)
    and bind_self_symbols mapping param_bindings =
      (* create bindings such as (P#cid, @self.value.cid) *)
      List.fold_left
        (fun mapping (id, expr') -> StringMap.add id expr' mapping)
        mapping
        param_bindings
    in
    let abstract_self = mk_abstract_self self in
    (* let role_label, (role_params,cnf) = abstract_self in
       print_endline @@ Printf.sprintf "unparsed abstract role %s" (unparse_constrained_role abstract_self);
       print_endline @@ Printf.sprintf "unparsed abstract role %s" (unparse_constrained_role (role_label, (role_params, (cnf_neg cnf)))); *)
    let self = [ self ]
    and trigger_ctxt = TriggerCtxt.init ~self
    and (projection : Projection.program list) =
      [ { events = []; relations = [] } ]
    and counter = ref 0
    and symbols_by_elem_uid = StringMap.empty
    and trigger_chain = []
    and symbols_by_trigger_string_env = Env.empty
    (* and trigger_expr_by_symbol = StringMap.empty *)
    and trigger_expr_by_symbol =
      wrap_self_as_prop_derefs () |> bind_self_symbols StringMap.empty
    and projected_events_env = Env.empty
    and sourcing_rx_relations_by_uid = StringMap.empty
    and control_flow_candidates_stack = [ [] ] in
    { abstract_self
    ; trigger_ctxt
    ; self (* encapsulated in trigger_ctxt *)
    ; trigger_chain (* encapsulated in trigger_ctxt *)
    ; projection
    ; counter
    ; symbols_by_elem_uid
    ; symbols_by_trigger_string_env
    ; trigger_expr_by_symbol
    ; projected_events_env
    ; sourcing_rx_relations_by_uid
    ; control_flow_candidates_stack
    }

  (* let initiator_of event_id t =
      (* trusting that preprocessing has checked initiator/receiver args *)
      (TriggerCtxt.participants_of event_id t.trigger_ctxt).initiator
  
    let receiver_of event_id t =
      (* trusting that preprocessing has checked initiator/receiver args *)
      (TriggerCtxt.participants_of event_id t.trigger_ctxt).receiver *)

  let self (ctxt : t) = List.hd ctxt.self

  let trigger_chain (ctxt : t) = ctxt.trigger_chain

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

  let control_flow_relations (ctxt : t) =
    List.hd ctxt.control_flow_candidates_stack

  let find_create_trigger_sym (trigger_string : string) (trigger_expr : expr')
      (ctxt : t) =
    match
      Env.find_flat_opt trigger_string ctxt.symbols_by_trigger_string_env
    with
    | Some sym -> (ctxt, sym)
    | None ->
      let count = !(ctxt.counter) in
      incr ctxt.counter;
      let fresh_sym = Symbols.next_trigger_val_sym () in
      let symbols_by_trigger_string_env =
        Env.bind trigger_string fresh_sym ctxt.symbols_by_trigger_string_env
      and trigger_expr_by_symbol =
        StringMap.add fresh_sym trigger_expr ctxt.trigger_expr_by_symbol
      in
      ( { ctxt with symbols_by_trigger_string_env; trigger_expr_by_symbol }
      , fresh_sym )

  let add_trigger_symbol_if_absent (trigger_string : string)
      (trigger_expr : expr') (ctxt : t) =
    match
      Env.find_flat_opt trigger_string ctxt.symbols_by_trigger_string_env
    with
    | Some _ -> ctxt
    | None ->
      let count = !(ctxt.counter) in
      incr ctxt.counter;
      let fresh_symbol = Printf.sprintf "@V%d" count in
      let symbols_by_trigger_string_env =
        Env.bind trigger_string fresh_symbol ctxt.symbols_by_trigger_string_env
      and trigger_expr_by_symbol =
        StringMap.add fresh_symbol trigger_expr ctxt.trigger_expr_by_symbol
      in
      { ctxt with symbols_by_trigger_string_env; trigger_expr_by_symbol }

  let bind_event_symbol (uid : element_uid) (sym : identifier) (t : t) =
    let symbols_by_elem_uid =
      StringMap.find_opt uid t.symbols_by_elem_uid
      |> Option.fold ~none:StringSet.empty ~some:Fun.id
      |> StringSet.add sym
      |> fun set -> StringMap.add uid set t.symbols_by_elem_uid
    in
    { t with symbols_by_elem_uid }

  let find_trigger_symbol (trigger_expr : string) (ctxt : t) =
    Env.find_flat_opt trigger_expr ctxt.symbols_by_trigger_string_env

  let include_projected_event (event_id : identifier)
      (projections : Projection.event list) (ctxt : t) =
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
  let push_ctrl_flow_relation (relation : Projection.relation) (ctxt : t) =
    let top = relation :: List.hd ctxt.control_flow_candidates_stack in
    let control_flow_candidates_stack =
      top :: List.tl ctxt.control_flow_candidates_stack
    in
    { ctxt with control_flow_candidates_stack }

  let begin_scope (trigger : Projection.event) (ctxt : t) =
    (* whoami *)
    let self = trigger.self :: ctxt.self
    and (projection : Projection.program list) =
      { events = []; relations = [] } :: ctxt.projection
    (* = projection; counter; symbols_by_elem_uid; .. = *)
    (* triggering event is added as nested level for resolving
       Initiator/Receiver expressions *)
    and trigger_chain =
      ((fst trigger.event'.data.info.data).data, trigger) :: ctxt.trigger_chain
    (* new scope to accumulate "@trigger" symbols created at this level;
       previous ones kept visible for constraint-evaluation purposes *)
    and symbols_by_trigger_string_env =
      Env.begin_scope ctxt.symbols_by_trigger_string_env
    (* start fresh each scope - @trigger expressions are only meaningful within
       the defining scope - TODO reassess *)
    (* and trigger_expr_by_symbol = StringMap.empty *)
    (* new scope to accumulate projected events - likely required to evaluate
       relations and projectability TODO [reassess] *)
    and projected_events_env = Env.begin_scope ctxt.projected_events_env
    and control_flow_candidates_stack =
      [] :: ctxt.control_flow_candidates_stack
    in
    { ctxt with
      self
    ; projection
    ; trigger_chain
    ; symbols_by_trigger_string_env
    ; projected_events_env
    ; control_flow_candidates_stack
    }

  let end_scope (ctxt : t) =
    let self = List.tl ctxt.self
    and projection = List.tl ctxt.projection
    and trigger_chain = Env.end_scope ctxt.trigger_chain
    and symbols_by_trigger_string_env =
      Env.end_scope ctxt.symbols_by_trigger_string_env
    and projected_events_env = Env.end_scope ctxt.projected_events_env
    and control_flow_candidates_stack =
      List.tl ctxt.control_flow_candidates_stack
    in
    { ctxt with
      self
    ; projection
    ; trigger_chain
    ; symbols_by_trigger_string_env
    ; projected_events_env
    ; control_flow_candidates_stack
    }
end

let rec project_spawn_program ctxt
    ({ events; relations } : Choreo.spawn_program) =
  project_events ctxt events >>= fun ctxt -> project_relations ctxt relations

and project_events ctxt (events : Choreo.event' list) =
  (* *)
  let rec project (ctxt : ProjectionContext.t) (event' : Choreo.event')
      ~(self : CnfRole.t) ~(projection_type : projection_t) :
      Projection.event list =
    let uid = Option.get !(event'.uid) in
    (* reminder: the marking must eventually be adjusted according to direct
       dependencies - an Rx is usually not excluded or pending, unless
       it represents a direct dep. to other events initialized by @self *)
    (* and marking = event'.data.marking.data in *)
    (*  *)
    (* generates a stringMap of symbol -> expr for symbols associated whith 
    this event *)
    let symbols =
      StringMap.find_opt uid ctxt.symbols_by_elem_uid
      |> Option.fold ~none:[] ~some:(fun set ->
             StringSet.elements set
             |> List.map (fun sym ->
                    (sym, StringMap.find sym ctxt.trigger_expr_by_symbol)))
      |> List.fold_left
           (fun acc (sym, expr') -> StringMap.add sym expr' acc)
           StringMap.empty
    in
    (* TODO revise - move constants *)
    let (res : Projection.event list) =
      begin
        match projection_type with
        | Local -> [ (uid, Projection.Local) ]
        | TxO receivers -> [ (uid ^ "_TxO", Projection.Tx receivers) ]
        | RxO initiators -> [ (uid ^ "_RxO", Projection.Rx initiators) ]
        | TxRx (receivers, initiators) ->
          [ (uid ^ "_Tx", Projection.Tx receivers)
          ; (uid ^ "_Rx", Projection.Rx initiators)
          ]
      end
      |> List.map (fun (uid, communication) : Projection.event ->
             { uid; event'; self; communication; symbols })
    in
    res
  and project_event (ctxt : ProjectionContext.t) (event' : event') =
    (* -----from event ctxt------ *)
    let self = ProjectionContext.self ctxt in
    let abstract_self = ctxt.abstract_self in
    (* ----------- *)
    let self_role = self.label
    and event_uid = Option.get !(event'.uid)
    and event_id = (fst event'.data.info.data).data in
    (* map participant-exprs to constrained roles: context-dependent
       due to Initiator/Receiver userset exprs *)
    let ctxt, (initiators, receivers, is_local) =
      ( event'.data.participants.data |> function
        | Choreo.Local init' -> (init', [], true)
        | Choreo.Interaction (init', recvrs) -> (init', recvrs, false) )
      |> fun (initr, rcvrs, is_local) ->
      let ctxt, constrained_initrs =
        to_constrained_role_exprs ctxt event_uid [ initr ]
      in
      let ctxt, constrained_recvrs =
        to_constrained_role_exprs ctxt event_uid rcvrs
      in
      (* DEBUGS *)
      (* print_endline
         @@ Printf.sprintf
              "@project_event: %s"
              (unparse_constrained_role (StringMap.find "P" constrained_initrs)); *)
      (ctxt, (constrained_initrs, constrained_recvrs, is_local))
    in

    let exclude_abstract_self (roles : CnfUserset.t) : CnfUserset.t =
      StringMap.find_opt self_role roles
      |> fold_role ~none:None ~some:(fun role ->
             CnfRole.resolve_role_diff role abstract_self)
      |> function
      | None -> roles
      | Some diff -> StringMap.add self_role diff roles
    in
    let self_as_initiator =
      StringMap.find_opt self_role initiators
      |> fold_role ~none:None ~some:(fun initr_role ->
             fold_role
               ~none:None
               ~some:(fun _ ->
                 CnfRole.resolve_role_intersection self initr_role)
               (CnfRole.resolve_role_intersection abstract_self initr_role))
    and self_as_receiver =
      StringMap.find_opt self_role receivers
      |> fold_role ~none:None ~some:(fun rcvr_role ->
             fold_role
               ~none:None
               ~some:(fun _ -> CnfRole.resolve_role_intersection self rcvr_role)
               (CnfRole.resolve_role_intersection abstract_self rcvr_role))
    in

    (* DEBUGS *)
    (* print_endline @@ Printf.sprintf "@project_event: %s" (unparse_constrained_role (StringMap.find "P" initiators)); *)

    (* ============ *)
    (* TODO (?) factorization/cleanup *)
    (* ===========  *)
    match (self_as_initiator, self_as_receiver) with
    | Some tx_role, Some rx_role -> begin
      let projections =
        if is_local then
          let self = tx_role in
          let projection_type = Local in
          project ctxt event' ~self ~projection_type
        else
          (* TODO comment on how corner cases are being handled *)
          (* We need to differentiate at least between:
               - being in a Tx-only subgroup
               - being in a Rx-only subgroup
               - being in the intersection of Tx with Rx - in a Tx/Rx dual
              However, there are corner cases to be handled, where the
              intersection might be just a user (a fully instantiated role),
              in which case we need to remove that user from the other end of
              the communication and map to a Tx-only or Rx-only event
          *)
          let dual_role_opt =
            Option.fold
              ~none:Option.none
              ~some:(fun role -> if is_user role then None else Some role)
              (CnfRole.resolve_role_intersection rx_role tx_role)
          and tx_only_cnf_opt =
            Option.fold
              ~none:
                (if is_user tx_role then
                   let receivers = CnfUserset.exclude_role receivers tx_role in
                   if CnfUserset.is_empty receivers then None
                   else Some (tx_role, receivers)
                 else None)
              ~some:(fun diff -> Some (diff, receivers))
              (CnfRole.resolve_role_diff tx_role rx_role)
          and rx_only_cnf_opt =
            Option.fold
              ~none:
                (if is_user rx_role then
                   let initiators =
                     CnfUserset.exclude_role initiators rx_role
                   in
                   if CnfUserset.is_empty initiators then None
                   else Some (tx_role, initiators)
                 else None)
              ~some:(fun diff -> Some (diff, initiators))
              (CnfRole.resolve_role_diff rx_role tx_role)
          in
          (* evaluate results *)
          let tx_only_cnf_res =
            match tx_only_cnf_opt with
            | None -> []
            | Some (self, receivers) ->
              let projection_type = TxO (exclude_abstract_self receivers) in
              project ctxt event' ~self ~projection_type
          in
          let rx_only_cnf_res =
            match rx_only_cnf_opt with
            | None -> []
            | Some (self, initiators) ->
              let projection_type = RxO (exclude_abstract_self initiators) in
              project ctxt event' ~self ~projection_type
          in
          let dual_cnf_res =
            match dual_role_opt with
            | None -> []
            | Some self ->
              let projection_type =
                TxRx
                  ( exclude_abstract_self receivers
                  , exclude_abstract_self initiators )
              in
              project ctxt event' ~self ~projection_type
          in
          tx_only_cnf_res @ rx_only_cnf_res @ dual_cnf_res
      in
      let ctxt =
        ProjectionContext.include_projected_event event_id projections ctxt
      in
      Ok ctxt
    end
    | Some tx_role, None ->
      let projections =
        if is_local then
          let self = tx_role in
          let projection_type = Local in
          project ctxt event' ~self ~projection_type
        else
          (* projecting for Tx *)
          let self = tx_role in
          let projection_type = TxO receivers in
          let tx_event = project ctxt event' ~self ~projection_type in
          tx_event
      in
      let ctxt =
        ProjectionContext.include_projected_event event_id projections ctxt
      in
      Ok ctxt
    | None, Some rx_role ->
      (* projecting for Rx *)
      let self = rx_role in
      let projection_type = RxO initiators in
      let rx_event = project ctxt event' ~self ~projection_type in
      let ctxt =
        ProjectionContext.include_projected_event event_id rx_event ctxt
      in
      Ok ctxt
    | None, None ->
      (* move on - no intersection *)
      Ok ctxt
  in
  fold_left_error project_event ctxt events

and project_relations (ctxt : ProjectionContext.t)
    (relations : Choreo.relation' list) =
  let rec project_spawn_relation (ctxt : ProjectionContext.t)
      (relation' : Choreo.relation') =
    let uid = Option.get !(relation'.uid) in
    match relation'.data with
    | Choreo.ControlRelation _ ->
      (* delay ctrl-flow relations until all spawn relations are projected, and
         on the recursion's way up *)
      Ok ctxt
    | Choreo.SpawnRelation (src_id', _expr', spawn_program) -> begin
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
      fold_left_error
        (fun (ctxt : ProjectionContext.t) (event : Projection.event) ->
          let ctxt = ProjectionContext.begin_scope event ctxt in
          project_spawn_program ctxt spawn_program
          >>= fun (ctxt : ProjectionContext.t) ->
          let projection = List.hd ctxt.projection in
          let src_uid = event.uid in
          let (spawn_relation : Projection.relation) =
            SpawnRelation (uid, (src_uid, src_id'.data), projection)
          in
          let ctxt = ProjectionContext.end_scope ctxt in
          let ctxt = ProjectionContext.add_relation ctxt spawn_relation in
          Ok ctxt)
        ctxt
        (Option.fold ~none:[] ~some:Fun.id src)
    end
  in
  let project_fst_degree_cf_rel (ctxt, acc) (relation' : Choreo.relation') =
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
              (fun (e1 : Projection.event) (e2 : Projection.event) ->
                Option.bind
                  (CnfRole.resolve_role_intersection e1.self e2.self)
                  (fun self -> Some (e1, e2, self)))
              srcs
              targets
            |> List.filter_map Fun.id
          in
          (* partition flow-control relations:
             {Local|Tx --> Local|Tx]} + {Rx -> Local|Tx} + {? -> Rx }
          *)
          let init_init, rx_init, x_rcv =
            List.partition
              (fun (_, (e2 : Projection.event), _) ->
                match e2.communication with
                | Local | Tx _ -> true
                | Rx _ -> false)
              candidates
            |> fun (x_init, x_rcv) ->
            let init_init, rx_init =
              List.partition
                (fun ((e1 : Projection.event), _, _) ->
                  match e1.communication with
                  | Local | Tx _ -> true
                  | Rx _ -> false)
                x_init
            in
            (init_init, rx_init, x_rcv)
          in
          (* project all {? -> Local|T} relations now, since they are
             straightfoward direct dependencies *)
          let ctxt, _ =
            List.fold_left_map
              (fun ctxt
                   ((e1 : Projection.event), (e2 : Projection.event), self)
                 ->
                let rel =
                  Projection.ControlFlowRelation
                    ( uid
                    , (e1.uid, (fst e1.event'.data.info.data).data)
                    , (e2.uid, (fst e2.event'.data.info.data).data)
                    , rel_type'.data
                    , self )
                in
                (ProjectionContext.add_relation ctxt rel, rel))
              ctxt
              (init_init @ rx_init)
          in
          (* make {Rx -> Local|T} relations visible to nested scopes - they
             need this to decide on "2nd degree" dependencies *)
          let ctxt, _ =
            List.fold_left_map
              (fun ctxt
                   ((e1 : Projection.event), (e2 : Projection.event), self)
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
          (* delay analysis of {? -> Rx } relations until after recursion
             bottoms out (i.e., all spawn relations projected) *)
          let acc =
            List.fold_left
              (fun acc
                   ((e1 : Projection.event), (e2 : Projection.event), self)
                 ->
                let rel =
                  Projection.ControlFlowRelation
                    ( uid
                    , (e1.uid, (fst e1.event'.data.info.data).data)
                    , (e2.uid, (fst e2.event'.data.info.data).data)
                    , rel_type'.data
                    , self )
                in
                rel :: acc)
              []
              x_rcv
            @ acc
          in
          Ok (ctxt, acc)
        | _ ->
          (* unles we have something projected at each end of the relation,
             the relation does not get a projection *)
          Ok (ctxt, acc)
      end
    | Choreo.SpawnRelation _ ->
      (* done on the recursion's way down *)
      Ok (ctxt, acc)
  (* TODO must further intersect self to ensure proper matching across scopes - use unions *)
  and project_snd_degree_cf_rel (ctxt : ProjectionContext.t)
      (relation : Projection.relation) =
    match relation with
    | Projection.ControlFlowRelation (_, _, (target_uid, _), rel_type_1, _self)
      ->
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
      Ok ctxt
    | Projection.SpawnRelation _ ->
      (* already handled on the recursion's way down *)
      Ok ctxt
  in
  fold_left_error project_fst_degree_cf_rel (ctxt, []) relations
  >>= fun (ctxt, delayed_ctrl_flows) ->
  fold_left_error project_spawn_relation ctxt relations >>= fun ctxt ->
  fold_left_error project_snd_degree_cf_rel ctxt delayed_ctrl_flows

and fold_role_cnf ~none ~some = function
  | None -> none
  | Some (label, (params, cnf)) -> Some (label, (params, some cnf))

and fold_role ~none ~some = function
  | None -> none
  | Some role -> some role

and to_constrained_role_exprs (ctxt : ProjectionContext.t)
    (event_uid : element_uid) (user_set_exprs : user_set_expr' list) :
    ProjectionContext.t * CnfUserset.t =
  List.fold_left
    (fun (ctxt, user_set) user_set_expr' ->
      let ctxt, roles =
        to_constrained_userset_expr ctxt (event_uid, user_set_expr')
      in
      (ctxt, List.fold_left CnfUserset.add_role user_set roles))
    (ctxt, CnfUserset.empty)
    user_set_exprs

(* convert a userset expression to constrained_role(s) form *)
and to_constrained_userset_expr (ctxt : ProjectionContext.t) (uid, userset_expr')
    : ProjectionContext.t * CnfRole.t list =
  (* stringify a @trigger.prop1.prop2... expression *)
  let rec stringify_trigger_expr ?(acc = "") expr' =
    match expr'.data with
    | Trigger label -> label ^ acc
    | PropDeref (base', prop') ->
      stringify_trigger_expr ~acc:(prop'.data ^ acc) base'
    | _ ->
      (* typechecker should be preventing any other pattern *)
      assert false
  (* convert a regular userset named_param' to a constrained-param *)
  and to_constrained_param ~ctxt named_param' :
      identifier' * cnf_formula * ProjectionContext.t =
    let name', value' = named_param'.data in
    (* let sym = symbol_of_param_name label ~ctxt name'.data in *)
    let param_sym = Symbols.encode_param_name name'.data in
    match value'.data with
    | Any -> (name', [], ctxt)
    | Expr expr' -> begin
      match expr'.data with
      | True -> (name', [ [ Positive (CnfEq (param_sym, BoolLit true)) ] ], ctxt)
      | False ->
        (name', [ [ Negative (CnfEq (param_sym, BoolLit true)) ] ], ctxt)
      | IntLit int_val ->
        (name', [ [ Positive (CnfEq (param_sym, IntLit int_val)) ] ], ctxt)
      | StringLit str_val ->
        (name', [ [ Positive (CnfEq (param_sym, StringLit str_val)) ] ], ctxt)
      | PropDeref _ ->
        (* reminder: typechecker should have already ensured this is a @trigger-based ref *)
        let stringified_trigger_expr = stringify_trigger_expr expr' in
        (*  TODO unify next 3 in one call *)
        let ctxt, sym =
          ProjectionContext.find_create_trigger_sym
            stringified_trigger_expr
            expr'
            ctxt
        in
        let ctxt = ProjectionContext.bind_event_symbol uid sym ctxt in
        (name', [ [ Positive (CnfSymEq (param_sym, sym)) ] ], ctxt)
      | _ ->
        (* if we're here, then typechecking must be extended *)
        assert false
    end
    | Alias _identifier' ->
      (* tentative: not yet in use *)
      assert false
    | RuntimeValue alias_opt' ->
      (* tentative: not yet in use *)
      assert false
  and constrained_role_of user_set_role_expr' : ProjectionContext.t * CnfRole.t
      =
    let label', params = user_set_role_expr'.data in
    let label = label'.data
    and ctxt, (param_types, encoding) =
      List.fold_left
        (fun (ctxt, (param_types, encoding)) param' ->
          let _, param_val' = param'.data in
          let param_ty = (Option.get !(param_val'.ty)).t_expr in
          let name', param_cnf, ctxt = to_constrained_param ~ctxt param' in
          let params = StringMap.add name'.data param_ty param_types in
          let cnf = cnf_and encoding param_cnf in
          (ctxt, (params, cnf)))
        (ctxt, (StringMap.empty, []))
        params
    in
    (ctxt, { label; param_types; encoding })
  (* map a userset expr into constrained roles *)
  and constrained_roles_of user_set_expr' =
    match user_set_expr'.data with
    | RoleExpr role_expr' ->
      constrained_role_of role_expr' |> fun (x, y) -> (x, [ y ])
    | Initiator event_id' ->
      let event = List.assoc event_id'.data ctxt.trigger_chain in
      begin
        match event.communication with
        | Local | Tx _ -> (ctxt, [ event.self ])
        | Rx initiators -> (ctxt, StringMap.bindings initiators |> List.map snd)
      end
    | Receiver event_id' ->
      let event = List.assoc event_id'.data ctxt.trigger_chain in
      begin
        match event.communication with
        | Local -> (* assume typechecking handled this (TODO) **) assert false
        | Tx receivers -> (ctxt, StringMap.bindings receivers |> List.map snd)
        | Rx _ -> (ctxt, [ event.self ])
      end
    (* | Diff (_roles_l, _roles_r) -> assert false *)
  in
  (* TODO (tentative, not a priority) multiple projection contexts at once *)
  constrained_roles_of userset_expr'

(** Entry Point *)
let rec project (program : Choreo.program) =
  let project_role ctxts ctxt =
    project_spawn_program ctxt program.spawn_program >>= fun ctxt ->
    tmp_debug ctxt;
    Ok (ctxt :: ctxts)
  (* setup one context per role declaration *)
  and init_ctxts =
    CnfUserset.of_role_decls program.roles
    |> CnfUserset.to_list
    |> List.map ProjectionContext.init
  in
  fold_left_error project_role [] init_ctxts

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
       \          %s"
       (ProjectionContext.self ctxt).label
       (Projection.unparse_projection (ProjectionContext.projection ctxt))
