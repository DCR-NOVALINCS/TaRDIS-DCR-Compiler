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
  | TxO of cnf_clause list * CnfUserset.t * user_set_expr' list
  | RxO of cnf_clause list * CnfUserset.t * user_set_expr' list
  | TxRx of
      (cnf_clause list * CnfUserset.t * user_set_expr' list)
      * (cnf_clause list * CnfUserset.t * user_set_expr' list)

(* TODO move somewhere else *)
module Projection = struct
  open Choreo

  type program =
    { events : event_t list
    ; relations : relation list
    }
  (* [example] local_binding : 'X' -> ('_@X0', _@trigger.initiator.cid) *)

  (** A placeholder for information required both during the projection process
      and for deriving the resulting endpoint event.

      [event'] choreography event linked to this endpoint-event

      [uid] the uid of the choreography [event'] (redundant, kept for
      convenience)

      [self] knowledge about the user observing this event's execution - as a
      role succesively unifies with events, either as an initator or a receiver,
      [self] accumulates implicit knowledge about the role which is subsequently
      propagated to potential nested scopes (monotonically narrows the role
      towards a user)

      [local_bindings] strictly expanding *)
  and event_t =
    { event' : Choreo.event'
    ; uid : identifier
    ; self : CnfRole.t
    ; local_bindings : (string * expr') StringMap.t
    ; implicit_bindings : cnf_clause list
    ; instantiation_constraints : cnf_formula
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
    | Tx of CnfUserset.t * user_set_expr' list
    | Rx of CnfUserset.t * user_set_expr' list

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
        | Tx (receivers, rcv_set) ->
          Printf.sprintf
            "[Tx]\n%s%s\n%s%s->  %s\n%s[Tx] @self -> %s"
            next_indent
            (CnfRole.to_string e.self)
            next_indent
            next_indent
            (unparse_participants receivers)
            next_indent
            (Frontend.Unparser.unparse_user_set_exprs rcv_set)
        | Rx (initiators, init_set) ->
          Printf.sprintf
            "[Rx]\n%s%s\n%s%s->  %s\n%s[Rx] %s -> @self"
            next_indent
            (unparse_participants initiators)
            next_indent
            next_indent
            (CnfRole.to_string e.self)
            next_indent
            (Frontend.Unparser.unparse_user_set_exprs init_set)
      and unparse_symbols () =
        List.map
          (fun (sym, expr') ->
            Printf.sprintf "%s:%s" sym (Frontend.Unparser.unparse_expr expr'))
          (StringMap.bindings e.symbols)
        |> String.concat ", " |> Printf.sprintf "(%s)"
      in
      Printf.sprintf
        "%s(uid:%s)  %s %s  %s\n%s@requires %s"
        indent
        e.uid
        (unparse_info ())
        (unparse_symbols ())
        (unparse_communication e.communication)
        indent
        (unparse_cnf_formula e.instantiation_constraints)
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

module Symbols : sig
  val next_trigger_val_sym : unit -> string

  val encodes_trigger_val_sym : string -> bool

  val next_bind_sym : unit -> string

  val encode_param_name : identifier -> string

  val encodes_param_name : string -> bool
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

  val init : self:CnfRole.t -> t

  val current_scope : t -> scope

  val self : t -> CnfRole.t

  

  val lookup_binding : identifier -> t -> (string * expr') option

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
  
  let init ~(self : CnfRole.t) =
    print_endline
    @@ Printf.sprintf
         "init trigger ctxt with self= %s\n\n"
         (CnfRole.to_string self);
    [ ( bootstrap_event_id
      , { self
      ; trigger_id = bootstrap_trigger_id
        ; implicit_bindings = []
        ; trigger_symbols = StringMap.empty
        ; trigger_chain = []
        ; trigger_exprs_by_sym = StringMap.empty
        ; bindings = StringMap.empty
        ; exprs_by_sym = Env.empty
        } )
    ]

  let current_scope (t : t) = snd (peek t)

  let self (t : t) = (snd (peek t)).self

  (* let lookup_expr_by_sym (sym:string) : (expr':Choreo.expr') =
    if Symbols.encodes_param_name sym  *)

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

  let initiators_of (event_id : event_id) (t : t) =
    let scope = snd (peek t) in
    let trigger_event = List.assoc event_id scope.trigger_chain in
    match trigger_event.communication with
    | Local | Tx _ -> [ trigger_event.self ]
    | Rx (initiators, _) -> StringMap.bindings initiators |> List.map snd

  let receivers_of (event_id : event_id) (t : t) =
    let scope = snd (peek t) in
    let trigger_event = List.assoc event_id scope.trigger_chain in
    match trigger_event.communication with
    | Local -> (* assume typechecking handled this (TODO) **) assert false
    | Tx (receivers, _) -> StringMap.bindings receivers |> List.map snd
    | Rx _ -> [ trigger_event.self ]

  let trigger_exprs (t : t) = (snd (peek t)).trigger_exprs_by_sym

  let begin_scope (trigger_id:identifier) (trigger : Projection.event_t) (t : t) : t =
    print_endline @@ "\n\n\   <<<<<<<<<<>>>>>>>>>>>  "  ^trigger_id;
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
      |> Env.bind_list (StringMap.bindings bindings |> List.map snd)
    in
    print_endline (Utils.Env.to_string ~fmt:Frontend.Unparser.unparse_expr exprs_by_sym); 
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

(**  *)
module CommunicationCtxt : sig
  (** [local_bindings] maps each locally-introduced bindings to its
      corresponding renaming and computation expression to eval on spawn, e.g.,
      for some binding #cid as X, {X -> (_@X0, _@trigger.initiator.cid)}) *)
  type t =
    { init_ctxt : RoleCtxt.t StringMap.t
    ; init_set : user_set_expr' list
    ; rcv_ctxt : RoleCtxt.t StringMap.t
    ; rcv_set : user_set_expr' list
    ; local_bindings : (string * expr') StringMap.t
    }

  val of_communication_expr : event_id -> participants -> TriggerCtxt.t -> TriggerCtxt.t * t

  val to_string : t -> string
end = struct
  open Choreo

  type t =
    { init_ctxt : RoleCtxt.t StringMap.t
    ; init_set : user_set_expr' list
    ; rcv_ctxt : RoleCtxt.t StringMap.t
    ; rcv_set : user_set_expr' list
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
    let trigger_ref_expr' = annotate (EventRef (annotate (Frontend.Syntax.trigger_id_of_event_id event_id))) in
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
        encode_named_param event_id
          (trigger_ctxt, role_ctxt, local_bindings)
          named_param')
      (trigger_ctxt, local_bindings, RoleCtxt.init_empty role'.data)
      params

  let encode_user_set_expr event_id (trigger_ctxt, local_bindings) user_set_expr' =
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
      user_set_role_expr_to_role_ctxt event_id (trigger_ctxt, local_bindings) role_expr'
      |> fun (a, b, c) -> (a, b, [ c ])
    | Initiator event_id' ->
      let init_set =
        TriggerCtxt.initiators_of event_id'.data trigger_ctxt |> to_role_ctxts
      in
      (trigger_ctxt, local_bindings, init_set)
    | Receiver event_id' ->
      let rcv_set =
        TriggerCtxt.receivers_of event_id'.data trigger_ctxt |> to_role_ctxts
      in
      (trigger_ctxt, local_bindings, rcv_set)

  let encode_user_set_exprs event_id (trigger_ctxt, local_bindings) user_set_exprs =
    List.fold_left
      (fun (trigger_ctxt, local_bindings, role_ctxts) user_set_expr' ->
        let trigger_ctxt, local_bindings, roles =
          encode_user_set_expr event_id (trigger_ctxt, local_bindings) user_set_expr'
        in
        ( trigger_ctxt
        , local_bindings
        , List.fold_left
            (fun roles_ctxts role_ctxt ->
              StringMap.add role_ctxt.RoleCtxt.role.label role_ctxt roles_ctxts)
            role_ctxts
            roles ))
      (trigger_ctxt, local_bindings, StringMap.empty)
      user_set_exprs

  (* let event = List.assoc event_id'.data ctxt.trigger_chain in
      begin
        match event.communication with
        | Local -> (* assume typechecking handled this (TODO) **) assert false
        | Tx receivers -> (ctxt, StringMap.bindings receivers |> List.map snd)
        | Rx _ -> (ctxt, [ event.self ])
      end *)
  (* ------------- *)
  (* | Diff (_roles_l, _roles_r) -> assert false *)

  (* TODO *)
  let of_communication_expr event_id (participants : Choreo.participants)
      (trigger_ctxt : TriggerCtxt.t) : TriggerCtxt.t * t =
    let trigger_ctxt, local_bindings, init_ctxt, rcv_ctxt, init_set, rcv_set =
      ( participants |> function
        | Choreo.Local init' -> (init', [])
        | Choreo.Interaction (init', recvrs) -> (init', recvrs) )
      |> fun (initrs, rcvrs) ->
      let trigger_ctxt, local_bindings, initiators =
        encode_user_set_exprs event_id (trigger_ctxt, StringMap.empty) [ initrs ]
      in
      let trigger_ctxt, local_bindings, receivers =
        encode_user_set_exprs event_id (trigger_ctxt, local_bindings) rcvrs
      in
      (trigger_ctxt, local_bindings, initiators, receivers, [ initrs ], rcvrs)
    in
    (trigger_ctxt, { local_bindings; init_ctxt; rcv_ctxt; init_set; rcv_set })

  (* TODO *)
  (* let lookup_initiator_role (role : role_label) : RoleCtxt.t option =
    Option.None

  (* TODO *)
  let lookup_receiver_role (role : role_label) : RoleCtxt.t option = Option.None *)
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
    { abstract_self : CnfRole.t
    ; trigger_ctxt : TriggerCtxt.t
    ; projection : Projection.program list
    ; projected_events_env : Projection.event_t list Env.t
    ; sourcing_rx_relations_by_uid :
        ((element_uid * event_id) * relation_type * CnfRole.t) list StringMap.t
    }

  let mk_abstract_self (self : CnfRole.t) : CnfRole.t =
    let label = self.label
    and param_label = "@self"
    and param_val = Sat.BoolLit true in
    let param_types = StringMap.empty |> StringMap.add param_label BoolTy
    and encoding = [ [ Positive (CnfEq (param_label, param_val)) ] ] in
    { label; param_types; encoding }

  let init (self : CnfRole.t) =
    (* add "abstract-self" marker to self's encoding *)
    let abstract_self = mk_abstract_self self in
    let trigger_ctxt =
      TriggerCtxt.init ~self:{ self with encoding = abstract_self.encoding }
    and (projection : Projection.program list) =
      [ { events = []; relations = [] } ]
    and projected_events_env = Env.empty
    and sourcing_rx_relations_by_uid = StringMap.empty in
    { abstract_self
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

  let begin_scope (trigger_id:identifier) (trigger : Projection.event_t) (ctxt : t) =
    let trigger_ctxt = TriggerCtxt.begin_scope trigger_id trigger ctxt.trigger_ctxt
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
    (user_set_expr' : user_set_expr') =
  (* (aux) rewrites a single user-set param *)
  let rewrite_user_set_param
      (user_set_param' : user_set_param_val' named_param') :
      user_set_param_val' named_param' =
    let rewrite_user_set_param_val = function
      | Expr expr' as expr -> begin
        match expr'.data with
        | EventRef binding' ->
          (* (reminder) EventRef reflects a binding in this context *)
          Expr (StringMap.find binding'.data bindings)
        | _ -> expr
      end
      | RuntimeValue binding_opt ->
        (* (reminder) Option is guaranteed to be Some - syntax will eventually 
          be adjusted to prevent this redundancy - however, a binding introduced 
      on the rhs might not be used on the lhs - in that case, replace with Any *)
        let sym = (Option.get binding_opt).data in
        Option.fold
          (StringMap.find_opt sym bindings)
          ~none:Any
          ~some:(fun expr' -> Expr expr')
      | _ as other -> other
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
  | Choreo.Initiator _ | Choreo.Receiver _ -> user_set_expr'
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

let rec project_spawn_program ctxt
    ({ events; relations } : Choreo.spawn_program) =
  project_events ctxt events |> fun ctxt -> project_relations ctxt relations

and project_events ctxt (events : Choreo.event' list) : ProjectionContext.t =
  (* *)
  let rec project (ctxt : ProjectionContext.t) (event' : Choreo.event')
      ~(self : CnfRole.t) ~(projection_type : projection_t)
      ~(local_bindings : (string * expr') StringMap.t) : Projection.event_t list
      =
    let uid = Option.get !(event'.uid)
    and base_self = ProjectionContext.self ctxt in

    (* self is the implicit role propagated to the inner scope *)

    (* reminder: the marking must eventually be adjusted according to direct
       dependencies - an Rx is usually not excluded or pending, unless
       it represents a direct dep. to other events initialized by @self *)
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
            , Projection.Tx (receivers, rcv_set) )
          ]
        | RxO (implicit_constraints, initiators, init_set) ->
          [ ( uid ^ "_RxO"
            , implicit_constraints
            , Projection.Rx (initiators, init_set) )
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
             (* reduce instantiation constraints to new knowledge, i.e., 
                to whatever was not already entailed by the @self *)
             let instantiation_constraints =
               extract_min_diff_constraint_set base_self.encoding self.encoding
               |> List.filter (fun c1 ->
                      not @@ List.exists (fun c2 -> c1 = c2) implicit_bindings)
               |> List.sort_uniq cnf_clause_compare
             in

             (* debug *)
             print_endline
             @@ Printf.sprintf
                  "\n\
                   Call to project with:\n\
                  \  > base_self:\t\t%s\n\
                  \  > self:\t\t%s\n\
                  \  > inst. constraints:\t%s\n"
                  (CnfRole.to_string base_self)
                  (CnfRole.to_string self)
                  (unparse_cnf_formula @@ instantiation_constraints);

             (* let rewrite_constraints (cnf:cnf_formula) (trigger_ctxt:) *)

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
             ; event'
             ; self
             ; communication
             ; symbols
             ; implicit_bindings
             ; instantiation_constraints
             ; local_bindings
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
    print_endline
    @@ Printf.sprintf
         "\n\n\n    >>>> called with event_id=%s   self=%s\n\n"
         event_id
         (CnfRole.to_string self);

    (* Tx/Rx events explicitly exclude @self from the "remote"-side *)
    let exclude_abstract_self (roles : CnfUserset.t) : CnfUserset.t =
      CnfUserset.exclude_role roles abstract_self
      (* StringMap.find_opt self_role roles
      |> fold_role ~none:None ~some:(fun role ->
             CnfRole.resolve_role_diff role abstract_self)
      |> function
      | None -> roles
      | Some diff -> StringMap.add self_role diff roles *)
    in

    let trigger_ctxt, communication_ctxt =
      CommunicationCtxt.of_communication_expr
      event_id
        event'.data.participants.data
        trigger_ctxt
    in
    let ctxt = { ctxt with trigger_ctxt } in

    (* debug *)
    print_endline @@ CommunicationCtxt.to_string communication_ctxt;

    let { local_bindings; init_ctxt; rcv_ctxt; _ } : CommunicationCtxt.t =
      communication_ctxt
    in

    let initrs, rcvrs =
      (derive_remote_participants init_ctxt, derive_remote_participants rcv_ctxt)
    in

    let resolve_unify_self (role : CnfRole.t) =
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
        print_endline
        @@ Printf.sprintf
             "\ntx_opt for role: %s"
             (CnfRole.to_string tx_ctxt.role);
        print_endline
        @@ Printf.sprintf "rx_opt for : %s\n" (CnfRole.to_string rx_ctxt.role);

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
    (* at this point, tx_opt and rx_opt (when Some) include the effective bindings
      (the ones they share) in their encoding *)

    (* let ctxt_res = *)
    match (tx_opt, rx_opt) with
    | Some tx_ctxt, Some rx_ctxt ->
      (* debug *)
      print_endline @@ Printf.sprintf "Role at both sides";

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
      print_endline
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
           (unparse_cnf_formula implicit_rx_only);

      (* TODO [revise] does it ever apply to rx? *)
      (* indicates whether tx/rx roles reduce to a user under all implicit constraints *)
      let is_implicit_tx_user, is_implicit_rx_user =
        let is_implicit_user (role : CnfRole.t) unbound_constraints =
          (not @@ is_user role)
          && is_user
             @@ { role with
                  encoding = cnf_and role.encoding unbound_constraints
                }
        in
        ( is_implicit_user tx_ctxt.role implicit_tx_only
        , is_implicit_user rx_ctxt.role implicit_rx_only )
      in

      (* debug *)
      print_endline
      @@ Printf.sprintf "\nrx is implicit user: %b" is_implicit_rx_user;
      print_endline
      @@ Printf.sprintf "tx is implicit user: %b\n" is_implicit_tx_user;

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
        ( derive_set rx_lead_local_bindings communication_ctxt.init_set
        , derive_set tx_lead_local_bindings communication_ctxt.rcv_set )
      in

      (* *)
      let tx_only_res =
        let project_tx_self (tx_only_role : CnfRole.t) =
          Option.fold
            (resolve_unify_self tx_only_role)
            ~none:[]
            ~some:(fun (self : CnfRole.t) ->
              let projection_type =
                let rcvrs =
                  if is_user tx_only_role then
                    CnfUserset.exclude_role rcvrs self
                  else rcvrs
                in
                TxO
                  ( tx_ctxt.implicit_constraints
                  , exclude_abstract_self rcvrs
                  , rcv_set )
              in
              project ctxt event' ~self ~projection_type ~local_bindings)
        in
        Option.fold
          (CnfRole.resolve_role_diff tx_ctxt.role rx_ctxt.role)
          ~none:
            (if is_user tx_ctxt.role then (
               print_endline "TxO with user on tx-side\n";
               project_tx_self tx_ctxt.role)
             else [])
          ~some:(fun diff_role -> project_tx_self diff_role)
      (* *)
      and rx_only_res =
        let project_rx_self rx_only_role =
          Option.fold
            (resolve_unify_self rx_only_role)
            ~none:[]
            ~some:(fun (self : CnfRole.t) ->
              let initrs =
                if is_user rx_only_role then CnfUserset.exclude_role initrs self
                else initrs
              in
              let projection_type =
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
          ~some:(fun diff_role -> project_rx_self diff_role)
      (*  *)
      (*  *)
      and tx_rx_res =
        Option.fold
          (CnfRole.resolve_role_intersection tx_ctxt.role rx_ctxt.role)
          ~none:[]
          ~some:(fun tx_rx_role ->
            (* TODO [move upstream, to projectability] - user sending a 
            message to itself does not make sense: communication has no
            effect *)
            (* assert (not (is_user tx_ctxt.role && is_user rx_ctxt.role)); *)
            if is_user tx_rx_role then (
              print_endline
                "tx_rx dual comes down to single user - discarding monologue";
              [])
            else (
              print_endline
              @@ Printf.sprintf
                   "tx_rx dual is a group: %s"
                   (CnfRole.to_string tx_rx_role);
              Option.fold
                (resolve_unify_self tx_ctxt.role)
                ~none:[]
                ~some:(fun (tx_rx_self_role : CnfRole.t) ->
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

                  project ctxt event' ~self ~projection_type ~local_bindings)))
      in

      let projections = tx_only_res @ tx_rx_res @ rx_only_res in

      ProjectionContext.include_projected_event event_id projections ctxt
    | Some tx_ctxt, None ->
      let rcv_set =
        List.map
          (rewrite_userset
             (TriggerCtxt.bindings trigger_ctxt
             |> StringMap.map (fun e -> snd e)))
          communication_ctxt.rcv_set
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
          communication_ctxt.init_set
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
      (relation' : Choreo.relation') =
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
          let (spawn_relation : Projection.relation) =
            SpawnRelation (uid, (src_uid, src_id'.data), projection)
          in
          let ctxt = ProjectionContext.end_scope ctxt in
          let ctxt = ProjectionContext.add_relation ctxt spawn_relation in
          ctxt)
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
              (fun (e1 : Projection.event_t) (e2 : Projection.event_t) ->
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
              (fun (_, (e2 : Projection.event_t), _) ->
                match e2.communication with
                | Local | Tx _ -> true
                | Rx _ -> false)
              candidates
            |> fun (x_init, x_rcv) ->
            let init_init, rx_init =
              List.partition
                (fun ((e1 : Projection.event_t), _, _) ->
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
                   ((e1 : Projection.event_t), (e2 : Projection.event_t), self)
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
          (* delay analysis of {? -> Rx } relations until after recursion
             bottoms out (i.e., all spawn relations projected) *)
          let acc =
            List.fold_left
              (fun acc
                   ((e1 : Projection.event_t), (e2 : Projection.event_t), self)
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
          (ctxt, acc)
        | _ ->
          (* unles we have something projected at each end of the relation,
             the relation does not get a projection *)
          (ctxt, acc)
      end
    | Choreo.SpawnRelation _ ->
      (* done on the recursion's way down *)
      (ctxt, acc)
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
      ctxt
    | Projection.SpawnRelation _ ->
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

(** Entry Point *)
let rec project (program : Choreo.program) =
  let project_role ctxts ctxt =
    project_spawn_program ctxt program.spawn_program |> fun ctxt ->
    tmp_debug ctxt;
    ctxt :: ctxts
  (* setup one context per role declaration *)
  and init_ctxts =
    CnfUserset.of_role_decls program.roles
    |> CnfUserset.to_list
    |> List.map ProjectionContext.init
  in
  List.fold_left project_role [] init_ctxts

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
