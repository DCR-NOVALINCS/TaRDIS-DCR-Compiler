open Sat
open Utils
open Utils.Results
open Userset_encoding
module Choreo = Frontend.Syntax
open Choreo
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let err_t_ambiguous_dep_on_dual_event =
  "[Failed projectability-check: ambiguous data-dependency on dual event]"

let rec peek : 'a. 'a list -> 'a = fun stack -> List.hd stack

and pop : 'a. 'a list -> 'a * 'a list =
 fun stack -> (List.hd stack, List.tl stack)

and push : 'a. 'a -> 'a list -> 'a list = fun elem stack -> elem :: stack

and update_top : ('a -> 'a) -> 'a list -> 'a list =
 fun update stack ->
  let top, tl = pop stack in
  push (update top) tl

(* TODO refactor *)

(** [list_combine f [a1; ...; an] [b1; ...; bm]] returns the list
    [[f a1 b1; f a1 b2; ...; f an bm]], resulting from applying function [f] to
    each element in the cartesian product of [[a1; ...; an]] and
    [[b1; ...; bm]]. *)
let list_combine : 'a 'b 'c. ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list =
 fun combinator l1 l2 ->
  List.concat (List.map (fun l1 -> List.map (fun l2 -> combinator l1 l2) l2) l1)

type rel_t =
  { src_id : event_id
  ; tgt_id : event_id
  ; rel_type : relation_type
  }

(* A dependency-graph targetting the collection of both data-based and direct
   dependencies *)
module DependencyGraph : sig
  (* type t *)

  type t

  val empty : t

  val on_ctrl_flow_rel_ : rel_t -> t -> t

  val outbound_state_based_deps : exec_based_rel:rel_t -> t -> rel_t list

  val inbound_exec_based_deps : state_based_rel:rel_t -> t -> rel_t list

  val to_string : t -> string
end = struct
  module RelSet = Set.Make (struct
    type t = rel_t

    let compare (left : t) (right : t) =
      let src_cmp = String.compare left.src_id right.src_id
      and tgt_cmp = String.compare left.src_id right.src_id in
      if src_cmp < 0 || src_cmp > 0 then src_cmp
      else if tgt_cmp < 0 || tgt_cmp > 0 then tgt_cmp
      else
        match (left.rel_type, right.rel_type) with
        | Include, Include
        | Exclude, Exclude
        | Response, Response
        | Condition, Condition
        | Milestone, Milestone -> 0
        | Include, _ -> 1
        | Exclude, (Response | Condition | Milestone) -> 1
        | Response, Condition | Response, Milestone -> 1
        | Condition, Milestone -> 1
        | _ -> -1
  end)

  type t =
    { state_based_rels_by_src : RelSet.t StringMap.t
    ; exec_based_rels_by_tgt : RelSet.t StringMap.t
    }

  (* Retrieves state-based dependencies following rel *)
  let outbound_state_based_deps ~exec_based_rel:(rel : rel_t) (t : t) =
    match rel.rel_type with
    | Condition | Milestone ->
      (* internal error *)
      assert false
    | _ ->
      Option.fold
        (StringMap.find_opt rel.tgt_id t.state_based_rels_by_src)
        ~none:[]
        ~some:(fun set ->
          RelSet.to_list set |> fun deps ->
          if rel.rel_type = Response then
            List.filter (fun r -> r.rel_type = Milestone) deps
          else deps)

  (* Retrieves exec-based dependencies preceding rel *)
  let inbound_exec_based_deps ~state_based_rel:(rel : rel_t) t =
    match rel.rel_type with
    | Include | Exclude | Response ->
      (* internal error *)
      assert false
    | _ ->
      Option.fold
        (StringMap.find_opt rel.src_id t.exec_based_rels_by_tgt)
        ~none:[]
        ~some:(fun set ->
          RelSet.to_list set |> fun deps ->
          if rel.rel_type = Condition then
            List.filter (fun r -> r.rel_type <> Response) deps
          else deps)

  let to_string (t : t) =
    let sprintf = Printf.sprintf in
    let rel_type_to_str ({ src_id; tgt_id; rel_type } : rel_t) =
      sprintf
        "{%s; %s; %s}"
        src_id
        tgt_id
        ((function
           | Include -> "-->+"
           | Exclude -> "-->%"
           | Response -> "*-->"
           | Condition -> "-->*"
           | Milestone -> "--><>")
           rel_type)
    in
    let dep_map_to_string dep_map =
      StringMap.map
        (fun set ->
          RelSet.to_list set |> List.map rel_type_to_str |> String.concat ", "
          |> sprintf "[%s]")
        dep_map
      |> StringMap.bindings
      |> List.map (fun (label, deps) -> sprintf "%s -> %s" label deps)
      |> String.concat "; " |> sprintf "[%s]"
    in
    sprintf
      "Dependency-graph:\n state-based deps: %s\n exec-based deps: %s"
      (dep_map_to_string t.state_based_rels_by_src)
      (dep_map_to_string t.exec_based_rels_by_tgt)

  (* ancillary *)
  (* let add_one ~src_uid ~tgt_uid dep_map =
    get_or_default src_uid dep_map |> StringSet.add tgt_uid |> fun set ->
    StringMap.add src_uid set dep_map *)

  (* ancillary *)
  (* let add_all key set dep_map =
    get_or_default key dep_map |> StringSet.union set |> fun set ->
    StringMap.add key set dep_map *)

  (* ancillary *)
  (* let add_foreach key_set dep dep_map =
    List.fold_left
      (fun dep_map key -> add_one key dep dep_map)
      dep_map
      (StringSet.elements key_set) *)

  let get_or_default key dep_map =
    Option.fold ~none:RelSet.empty ~some:Fun.id (StringMap.find_opt key dep_map)

  let on_state_based_dep (rel : rel_t) (t : t) =
    { t with
      state_based_rels_by_src =
        ( get_or_default rel.src_id t.state_based_rels_by_src |> RelSet.add rel
        |> fun set -> StringMap.add rel.src_id set t.state_based_rels_by_src )
    }

  let on_exec_based_dep (rel : rel_t) (t : t) =
    { t with
      exec_based_rels_by_tgt =
        ( get_or_default rel.tgt_id t.exec_based_rels_by_tgt |> RelSet.add rel
        |> fun set -> StringMap.add rel.tgt_id set t.exec_based_rels_by_tgt )
    }

  let empty =
    { exec_based_rels_by_tgt = StringMap.empty
    ; state_based_rels_by_src = StringMap.empty
    }

  let on_ctrl_flow_rel_ (rel : rel_t) (t : t) =
    match rel.rel_type with
    | Condition | Milestone -> on_state_based_dep rel t
    | Response | Include | Exclude -> on_exec_based_dep rel t
end

module Symbols : sig
  val next_trigger_val_sym : unit -> event_id

  val next_param_val_sym : unit -> event_id

  val encodes_param_val_sym : event_id -> bool

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

  let next_trigger_val_sym () =
    Printf.sprintf "%s%d" trigger_sym_val_prefix @@ next_int ()

  and next_param_val_sym () =
    Printf.sprintf "%s%d" param_sym_val_prefix @@ next_int ()

  and encodes_param_val_sym identifier =
    String.starts_with ~prefix:param_sym_val_prefix identifier

  and next_bind_sym () =
    Printf.sprintf "%s%d" param_bind_sym_prefix @@ next_int ()

  and encode_param_name identifier =
    Printf.sprintf "%s%s" param_name_prefix identifier

  and encodes_param_name identifier =
    String.starts_with ~prefix:param_name_prefix identifier
end

module TriggerCtxt : sig
  type t

  (*
     = initiator = @trigger.initiator (user); with each triggering of an interaction,
     every receiver (if any) observes the same initiator within a corresponding spawn.
     = receiver = @trigger.receiver (user); with each triggering of an interaction,
     initiator observes one receiver (if any) per each corresponding spawn.
     = all = @trigger.initiator (user) + @trigger.all_receivers (group, if any); with
     each triggering of an interaction, the overall participants involved are the
     initiator and the receive-group
  *)
  and participants =
    { initiator : CnfRole.t
    ; receiver : CnfRole.t option
    ; all : CnfUserset.t
    }

  and scope =
    { participants : participants
    ; trigger_symbols : string StringMap.t
    ; bindings : string StringMap.t
    }

  val init : CnfUserset.t -> t

  val trigger_sym_of : expr' -> t -> t * string

  val begin_scope : event_id -> participants -> string StringMap.t -> t -> t

  val end_scope : t -> t

  val participants_in_scope : t -> CnfUserset.t

  val participants_of : event_id -> t -> participants

  val find_trigger_ctxt : event_id -> t -> scope

  val defines_binding : identifier -> t -> bool

  val lookup_binding : identifier -> t -> string option

  val to_string : t -> string
end = struct
  exception Internal_error of string

  type t = (event_id * scope) list

  and scope =
    { participants : participants
    ; trigger_symbols : string StringMap.t
    ; bindings : string StringMap.t
    }

  and participants =
    { initiator : CnfRole.t
    ; receiver : CnfRole.t option
    ; all : CnfUserset.t
    }

  let bootstrap_initiator : CnfRole.t =
    { label = "#ROOT"; param_types = StringMap.empty; encoding = [] }

  and bootstrap_event_id = "#bootstrap"

  let init (participants : CnfUserset.t) : t =
    let participants =
      { initiator = bootstrap_initiator; receiver = None; all = participants }
    and trigger_symbols = StringMap.empty
    and bindings = StringMap.empty in
    [ (bootstrap_event_id, { participants; trigger_symbols; bindings }) ]

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

  let begin_scope (event_id : event_id) participants bindings (t : t) : t =
    let _, scope = peek t in
    let bindings =
      StringMap.union (fun _ v _ -> Some v) scope.bindings bindings
    in
    let scope = { bindings; participants; trigger_symbols = StringMap.empty } in
    push (event_id, scope) t

  let end_scope t = snd @@ pop t

  let participants_in_scope (t : t) = (snd (peek t)).participants.all

  let participants_of (event_id : event_id) (t : t) =
    let { participants; _ } = List.assoc event_id t in
    participants

  let find_trigger_ctxt (event_id : event_id) (t : t) = List.assoc event_id t

  let to_string t =
    let participant_map_to_str map =
      StringMap.bindings map
      |> List.map (fun (_, role) ->
             Printf.sprintf "  %s" (CnfRole.to_string role))
      |> String.concat "\n" |> Printf.sprintf "%s"
    in
    let participants_to_str { initiator; receiver; all } =
      let initr = CnfRole.to_string initiator
      and rcvr =
        Option.fold
          ~none:"None"
          ~some:(fun rcvr -> CnfRole.to_string rcvr)
          receiver
      and participants = participant_map_to_str all in
      Printf.sprintf
        "{ initiator= %s\n; receiver= %s\n;  participants= %s\n}\n"
        initr
        rcvr
        participants
    in
    let bindings_as_str bindings =
      StringMap.bindings bindings
      |> List.map (fun (k, v) -> Printf.sprintf "%s->%s" k v)
      |> String.concat ", " |> Printf.sprintf "[%s]"
    and trigger_symbols_to_str trigger_symbols =
      List.map
        (fun (k, v) -> Printf.sprintf "%s= %s" k v)
        (StringMap.bindings trigger_symbols)
      |> String.concat ", "
    in
    let scope_to_string (scope : scope) =
      Printf.sprintf
        "= trigger_symbols:\n%s"
        (trigger_symbols_to_str scope.trigger_symbols)
      |> Printf.sprintf
           "= participants:\n%s\n%s"
           (participants_to_str scope.participants)
      |> Printf.sprintf
           "\n@projectability.ml [TriggerCtxt.t debug]\n= Bindings: %s\n%s"
           (bindings_as_str scope.bindings)
    in
    List.map
      (fun (event_id, scope) ->
        Printf.sprintf "%s -> %s\n" event_id (scope_to_string scope))
      t
    |> String.concat ",\n"

  let bindings t = (snd @@ peek t).bindings

  let defines_binding identifier t =
    if List.is_empty t then false else StringMap.mem identifier (bindings t)

  let lookup_binding declared_sym t =
    StringMap.find_opt declared_sym (bindings t)
end

module RoleCtxt : sig
  (* TODO document - these can be union roles, including the user - must
     solve to extract every solution to the SAT problem encoded by the
     constrained role *)
  type t =
    { base : CnfRole.t
    ; group : CnfRole.t
    ; users : CnfRole.t
    ; defined_aliases : string StringMap.t
    }

  exception Internal_error of string

  val of_role_expr :
       TriggerCtxt.t
    -> string StringMap.t
    -> userset_role_expr'
    -> TriggerCtxt.t * string StringMap.t * t

  val of_constrained_user_role : CnfRole.t -> t

  val role_label : t -> event_id

  (* requires: same role - fails otherwise *)
  val union : t -> t -> t

  val to_string : ?indent:string -> t -> string
end = struct
  type t =
    { base : CnfRole.t
    ; group : CnfRole.t
    ; users : CnfRole.t
    ; defined_aliases : string StringMap.t
    }

  exception Internal_error of string

  let to_string ?(indent = "") t =
    let base = Printf.sprintf "  base: %s" @@ CnfRole.to_string t.base
    and group = Printf.sprintf " group: %s" @@ CnfRole.to_string t.group
    and users = Printf.sprintf " users: %s" @@ CnfRole.to_string t.users
    and defined_aliases =
      StringMap.bindings t.defined_aliases
      |> List.map (fun (k, v) -> Printf.sprintf "%s->%s" k v)
      |> String.concat ", "
      |> Printf.sprintf " defined_aliases: %s"
    in
    Printf.sprintf
      "\n%s{ %s\n%s;  %s\n%s;  %s\n%s;  %s\n%s}"
      indent
      base
      indent
      group
      indent
      users
      indent
      defined_aliases
      indent

  let role_label t = t.base.label

  let _extract_user_param_assignments (params : StringSet.t) (cnf : cnf_formula)
      =
    let rec extract_from_cnf_clause param_name = function
      | [] -> None
      | lit :: xs -> begin
        match lit with
        | Positive (CnfSymEq (s1, s2)) ->
          if s1 = param_name && Symbols.encodes_param_val_sym s2 then Some s2
          else if s2 = param_name && Symbols.encodes_param_val_sym s1 then
            Some s1
          else extract_from_cnf_clause param_name xs
        | _ -> extract_from_cnf_clause param_name xs
      end
    (* obs: it's an implementation error to call this if [param_name] 
      is not assigned within [cnf] (check first) *)
    and extract_from_cnf_formula param_name (cnf : cnf_formula) =
      Option.fold
        (List.find_map (extract_from_cnf_clause param_name) cnf)
        ~none:(assert false)
        ~some:Fun.id
    in
    List.fold_left
      (fun acc param_name ->
        StringMap.add param_name (extract_from_cnf_formula param_name cnf) acc)
      StringMap.empty
      (StringSet.elements params)

  (* extract group-view free params *)
  let _extract_free_params (t : t) =
    let rec assigned_in_cnf_clause ?(acc = StringSet.empty) = function
      | [] -> acc
      | lit :: xs -> begin
        match lit with
        | Positive (CnfSymEq (s1, s2)) | Negative (CnfSymEq (s1, s2)) ->
          if Symbols.encodes_param_name s1 && Symbols.encodes_param_val_sym s2
          then assigned_in_cnf_clause ~acc:(StringSet.add s1 acc) xs
          else if
            Symbols.encodes_param_name s2 && Symbols.encodes_param_val_sym s1
          then assigned_in_cnf_clause ~acc:(StringSet.add s2 acc) xs
          else assigned_in_cnf_clause ~acc xs
        | _ -> assigned_in_cnf_clause ~acc xs
      end
    and assigned_in_cnf_formula ?(acc = StringSet.empty) = function
      | [] -> acc
      | clause :: xs ->
        let acc = StringSet.union acc (assigned_in_cnf_clause clause) in
        assigned_in_cnf_formula ~acc xs
    in
    StringSet.diff
      (assigned_in_cnf_formula t.group.encoding)
      (StringMap.bindings t.base.param_types
      |> List.map fst |> StringSet.of_list)

  let union (left : t) (right : t) : t =
    if role_label left <> role_label right then
      raise @@ Internal_error "Expecting arguments of same role"
    else
      (* note: we know what we encoded, this must result in a valid role *)
      let base =
        Option.get @@ CnfRole.resolve_role_union left.base right.base
      in
      let group =
        Option.get @@ CnfRole.resolve_role_union left.group right.group
      in
      let free_params_common =
        StringSet.inter (_extract_free_params left) (_extract_free_params right)
      in
      let users =
        if StringSet.is_empty free_params_common then
          Option.get @@ CnfRole.resolve_role_union left.users right.users
        else
          (* unify free params under common param_sym  *)
          Option.get @@ CnfRole.resolve_role_union left.users right.users
      in
      let defined_aliases =
        StringMap.union
          (fun _ v _ -> Some v)
          left.defined_aliases
          right.defined_aliases
      in
      { base; group; users; defined_aliases }

  let of_constrained_user_role (constrained_user_role : CnfRole.t) =
    { base = constrained_user_role
    ; group = constrained_user_role
    ; users = constrained_user_role
    ; defined_aliases = StringMap.empty
    }

  let rec of_role_expr (trigger_ctxt : TriggerCtxt.t)
      (local_bindings : string StringMap.t) (role_expr' : userset_role_expr') =
    let role', params = role_expr'.data in
    let trigger_ctxt, local_bindings, role_ctxt =
      List.fold_left
        (fun (trigger_ctxt, event_bindings, role_ctxt) param' ->
          add_named_param trigger_ctxt event_bindings param' role_ctxt)
        (trigger_ctxt, local_bindings, init_role_ role'.data)
        params
    in
    (trigger_ctxt, local_bindings, role_ctxt)

  and init_role_ label =
    let unconstrained_role : CnfRole.t =
      { label; param_types = StringMap.empty; encoding = [] }
    in
    { base = unconstrained_role
    ; group = unconstrained_role
    ; users = unconstrained_role
    ; defined_aliases = StringMap.empty
    }

  and add_named_param (trigger_ctxt : TriggerCtxt.t) local_bindings named_param'
      t : TriggerCtxt.t * string StringMap.t * t =
    let name', value' = named_param'.data in
    let named_param_ty = (name'.data, (Option.get !(value'.ty)).t_expr) in
    let t = add_param_ty named_param_ty t in
    let name_sym = Symbols.encode_param_name name'.data in
    match value'.data with
    | Any -> (trigger_ctxt, local_bindings, encode_free_param name_sym t)
    | Expr expr' ->
      encode_from_param_expr trigger_ctxt local_bindings name_sym expr' t
    | Alias _identifier' ->
      (* TODO resolve this - param=alias is actually encoded as Expr of expr' above *)
      (* encode_from_param_expr name_sym expr' trigger_ctxt t *)
      assert false
      (* , encode_param_binding_usage_ trigger_ctxt name'.data identifier'.data t *)
    | RuntimeValue alias_opt' ->
      Option.fold
        ~none:(trigger_ctxt, local_bindings, encode_free_param name_sym t)
        ~some:(fun identifier' ->
          let local_bindings, role_ctxt =
            on_param_binding local_bindings name_sym identifier'.data t
          in
          (trigger_ctxt, local_bindings, role_ctxt))
        alias_opt'

  and encode_from_param_expr trigger_ctxt local_bindings param_sym expr' t =
    let rec to_constrained_param trigger_ctxt local_bindings param_sym expr' =
      match expr'.data with
      | True ->
        (trigger_ctxt, [ Positive (CnfEq (param_sym, BoolLit true)) ], true)
      | False ->
        (trigger_ctxt, [ Negative (CnfEq (param_sym, BoolLit false)) ], true)
      | IntLit int_val ->
        (trigger_ctxt, [ Positive (CnfEq (param_sym, IntLit int_val)) ], true)
      | StringLit str_val ->
        (trigger_ctxt, [ Positive (CnfEq (param_sym, StringLit str_val)) ], true)
      | PropDeref _ ->
        (* trusting that preprocessing prevents other patterns here *)
        let trigger_ctxt, trigger_sym =
          TriggerCtxt.trigger_sym_of expr' trigger_ctxt
        in
        (trigger_ctxt, [ Positive (CnfSymEq (param_sym, trigger_sym)) ], true)
      | EventRef id' -> begin
        match TriggerCtxt.lookup_binding id'.data trigger_ctxt with
        | None ->
          let bind_sym = StringMap.find id'.data local_bindings in
          (trigger_ctxt, [ Positive (CnfSymEq (param_sym, bind_sym)) ], false)
        | Some bind_sym ->
          (trigger_ctxt, [ Positive (CnfSymEq (param_sym, bind_sym)) ], true)
      end
      | _ -> assert false
    in
    let trigger_ctxt, clause, is_binding =
      to_constrained_param trigger_ctxt local_bindings param_sym expr'
    in
    let base = if is_binding then add_clause_ t.base clause else t.base
    and group = add_clause_ t.group clause
    and users = add_clause_ t.users clause in
    ( trigger_ctxt
    , local_bindings
    , { base; group; users; defined_aliases = StringMap.empty } )

  and on_param_binding local_bindings param_name binding t =
    let bind_sym = Symbols.next_bind_sym () in
    let local_bindings = StringMap.add binding bind_sym local_bindings in
    let clause = [ Positive (CnfSymEq (param_name, bind_sym)) ] in
    let group = add_clause_ t.group clause in
    let users = add_clause_ t.users clause in
    let defined_aliases = StringMap.add binding bind_sym t.defined_aliases in
    (local_bindings, { t with group; users; defined_aliases })

  and encode_free_param name (t : t) =
    let sym = Symbols.next_param_val_sym () in
    let clause = [ Positive (CnfSymEq (name, sym)) ] in
    let users = add_clause_ t.users clause in
    (* add_param_ty named_param_ty t |> fun t ->  *)
    { t with users }

  and add_clause_ cnf_role (clause : cnf_clause) : CnfRole.t =
    { cnf_role with encoding = cnf_and cnf_role.encoding [ clause ] }

  and add_param_ty (name, type_expr) (t : t) =
    let param_types = StringMap.add name type_expr t.base.param_types in
    let base = { t.base with param_types }
    and group = { t.group with param_types }
    and users = { t.users with param_types } in
    { t with base; group; users }
end

module EventCtxt : sig
  type t =
    { event' : Choreo.event'
    ; uid : element_uid
    ; id : event_id
    ; init_ctxt : RoleCtxt.t StringMap.t
    ; rcv_ctxt : RoleCtxt.t StringMap.t
    ; bindings : string StringMap.t
    }

  val init :
       Choreo.event'
    -> TriggerCtxt.t
    -> uid:element_uid
    -> id:identifier
    -> initiator:user_set_expr'
    -> receivers:user_set_expr' list
    -> TriggerCtxt.t * t

  val base_initiators : t -> CnfUserset.t

  val base_receivers : t -> CnfUserset.t

  val base_participants : t -> CnfUserset.t

  val resolve_trigger_participants :
    t -> (CnfRole.t * CnfRole.t option * CnfUserset.t) list

  val to_string : ?indent:string -> t -> string
end = struct
  type t =
    { event' : Choreo.event'
    ; uid : element_uid
    ; id : event_id
    ; init_ctxt : RoleCtxt.t StringMap.t
    ; rcv_ctxt : RoleCtxt.t StringMap.t
    ; bindings : string StringMap.t
    }

  (* and interaction_group = RoleCtxt.t StringMap.t *)

  let rec init (event' : Choreo.event') trigger_ctxt ~uid ~id
      ~(initiator : user_set_expr') ~(receivers : user_set_expr' list) =
    let trigger_ctxt, bindings, init_ctxt =
      process_init_recv_expr trigger_ctxt StringMap.empty [ initiator ]
    in
    let trigger_ctxt, bindings, rcv_ctxt =
      process_init_recv_expr trigger_ctxt bindings receivers
    in
    (trigger_ctxt, { event'; uid; id; init_ctxt; rcv_ctxt; bindings })

  (*
    Process the user-set expressions corresponding to either the initiator or 
    receiver side; event processing is context-dependent and a single event may
    be processed under different contexts, namely, for distinct 
    initiator/receiver expressions.
  *)
  and process_init_recv_expr (trigger_ctxt : TriggerCtxt.t)
      (local_bindings : string StringMap.t)
      (userset_exprs : user_set_expr' list) :
      TriggerCtxt.t * string StringMap.t * RoleCtxt.t StringMap.t =
    let rec group_by_role ?(grouped = StringMap.empty) = function
      | [] -> grouped
      | role_ctxt :: xs ->
        let role_label = RoleCtxt.role_label role_ctxt in
        let grouped =
          Option.fold
            ~none:(StringMap.add role_label role_ctxt grouped)
            ~some:(fun other ->
              StringMap.add role_label (RoleCtxt.union role_ctxt other) grouped)
            (StringMap.find_opt role_label grouped)
        in
        group_by_role ~grouped xs
    in
    List.fold_left
      (fun (trigger_ctxt, local_bindings, role_ctxts) userset_expr' ->
        let trigger_ctxt, local_bindings, role_ctxt =
          user_set_expr_to_role_ctxt trigger_ctxt local_bindings userset_expr'
        in
        let role_ctxts = role_ctxt :: role_ctxts in
        (trigger_ctxt, local_bindings, role_ctxts))
      (trigger_ctxt, local_bindings, [])
      userset_exprs
    |> fun (trigger_ctxt, local_bindings, role_ctxts) ->
    (trigger_ctxt, local_bindings, group_by_role role_ctxts)

  (*
       process one user-set expression to role_ctxt
    *)
  and user_set_expr_to_role_ctxt trigger_ctxt local_bindings userset_expr' =
    match userset_expr'.data with
    | RoleExpr role_expr' ->
      let trigger_ctxt, local_bindings, role_ctxt =
        RoleCtxt.of_role_expr trigger_ctxt local_bindings role_expr'
      in
      (trigger_ctxt, local_bindings, role_ctxt)
    | Initiator event_id' ->
      let init_ctxt =
        (TriggerCtxt.participants_of event_id'.data trigger_ctxt).initiator
        |> RoleCtxt.of_constrained_user_role
      in
      (trigger_ctxt, local_bindings, init_ctxt)
    | Receiver event_id' ->
      let rcv_ctxt =
        (TriggerCtxt.participants_of event_id'.data trigger_ctxt).receiver
        |> Option.get |> RoleCtxt.of_constrained_user_role
      in
      (trigger_ctxt, local_bindings, rcv_ctxt)
  (* | Diff (_roles_l, _roles_r) -> assert false *)

  (* TODO reassess *)

  (*
     let group_participants (t : t) =
       StringMap.map (fun role_ctxt -> role_ctxt.RoleCtxt.group) (participants t)

     let user_participants (t : t) =
       StringMap.map (fun role_ctxt -> role_ctxt.RoleCtxt.users) (participants t) *)

  let base_initiators (t : t) : CnfUserset.t =
    StringMap.map (fun role_ctxt -> role_ctxt.RoleCtxt.base) t.init_ctxt

  let base_receivers (t : t) : CnfUserset.t =
    StringMap.map (fun role_ctxt -> role_ctxt.RoleCtxt.base) t.rcv_ctxt

  let rec base_participants (t : t) =
    StringMap.map (fun role_ctxt -> role_ctxt.RoleCtxt.base) (participants t)

  and participants (t : t) =
    StringMap.union
      (fun _ left right -> Some (RoleCtxt.union left right))
      t.init_ctxt
      t.rcv_ctxt

  let add_user interaction_group (user : CnfRole.t) =
    let user_ctxt = RoleCtxt.of_constrained_user_role user in
    Option.fold
      ~none:(StringMap.add user.label user_ctxt interaction_group)
      ~some:(fun role_ctxt ->
        StringMap.add
          user.label
          (RoleCtxt.union user_ctxt role_ctxt)
          interaction_group)
      (StringMap.find_opt user.label interaction_group)

  let rec resolve_initiators t =
    resolve_users (StringMap.bindings t.init_ctxt |> List.map snd)

  and resolve_receivers t =
    resolve_users (StringMap.bindings t.rcv_ctxt |> List.map snd)

  (* TODO document
     returns all possible combinantions of (initiator, receiver, participants)
     by
     picking a representative for each disjoint participant-set in each role, in
       initiators: the initiator
     picking a representative for each disjoint participant-set in each role, in
       receivers: the receiver
     for each initiator, participants is the receiver-group + the initiator
  *)
  and resolve_trigger_participants t =
    let initr_users = resolve_initiators t |> List.flatten
    and rcvr_users =
      resolve_receivers t |> List.flatten |> fun lst ->
      if List.is_empty lst then [ None ] else List.map Option.some lst
    in
    initr_users
    |> list_combine
         (fun role_ctxts init_user ->
           (init_user, add_user role_ctxts init_user))
         [ t.rcv_ctxt ]
    |> List.map (fun (init, ctxt_roles) ->
           ( init
           , StringMap.map
               (fun ctxt_role -> ctxt_role.RoleCtxt.group)
               ctxt_roles ))
    |> list_combine
         (fun rcvr (init, participants) -> (init, rcvr, participants))
         rcvr_users

  (* returns a list of lists, with one entry per role in role_ctxts containing
     all solutions for the SAT problem that role encodes *)
  and resolve_users role_ctxts =
    List.fold_left
      (fun users role_ctxt ->
        let user_ctxt = role_ctxt.RoleCtxt.users in
        (cnf_all_sat_solve user_ctxt.encoding
        |> List.map (fun encoding : CnfRole.t ->
               { label = user_ctxt.CnfRole.label
               ; param_types = user_ctxt.param_types
               ; encoding
               }))
        :: users)
      []
      role_ctxts

  (* tmp debug *)
  let to_string ?(indent = "") t =
    let sprintf = Printf.sprintf
    and participant_map_to_str participants =
      StringMap.bindings participants
      |> List.map (fun (_, role_ctxt) ->
             Printf.sprintf
               "  %s"
               (RoleCtxt.to_string ?indent:(Some "    ") role_ctxt))
      |> String.concat "\n" |> Printf.sprintf "%s"
    in
    let uid = sprintf "uid: %s" t.uid
    and id = sprintf "id: %s" t.id
    and init_ctxt = sprintf "init_ctxt: %s" (participant_map_to_str t.init_ctxt)
    and rcv_ctxt = sprintf "rcv_ctxt: %s" (participant_map_to_str t.rcv_ctxt)
    and bindings =
      sprintf
        "event_level_bindings: %s"
        (StringMap.bindings t.bindings
        |> List.map (fun (k, v) -> sprintf "%s->%s" k v)
        |> String.concat ", ")
    in
    sprintf
      "%s{ %s%s\n%s; %s\n%s; %s\n%s; %s\n%s; %s\n%s}"
      indent
      indent
      uid
      indent
      id
      indent
      init_ctxt
      indent
      rcv_ctxt
      indent
      bindings
      indent
end

(* Indicates whether a cnf solution (unit clauses only) excludes multiple
   symbolic assignments to the same parameter - we prevent this to correctly
   handle static verification of bindings, where we conservatively interpret
   different symbols as an indication of distinct values. *)

let cnf_unique_param_assignment cnf_sol =
  let resolve_assignment param_sym assigned ok_status =
    if StringSet.mem param_sym assigned then (assigned, false)
    else (StringSet.add param_sym assigned, ok_status)
  in
  let on_unexpected_encoding () =
    (* Safety check - something in the implementation has unexpectedly
       changed and the approach needs to be revised *)
    assert false
  in
  (* obs: slightly more defensive than needed, but it may be hard to trace
     errors back to this method otherwise - safeguard against unexpected
     changes *)
  let cnf_unique_param_assignment (assigned, ok_status) = function
    | [ Positive (CnfSymEq (sym1, sym2)) ] ->
      let param_sym =
        if
          Symbols.encodes_param_name sym1
          && not (Symbols.encodes_param_name sym2)
        then sym1
        else if
          Symbols.encodes_param_name sym2
          && not (Symbols.encodes_param_name sym1)
        then sym2
        else on_unexpected_encoding ()
      in
      resolve_assignment param_sym assigned ok_status
    | [ Positive (CnfEq (param_sym, _)) ] ->
      if Symbols.encodes_param_name param_sym then
        resolve_assignment param_sym assigned ok_status
      else on_unexpected_encoding ()
    | _ -> (assigned, ok_status)
  in
  List.fold_left cnf_unique_param_assignment (StringSet.empty, true) cnf_sol

(* TODO [revisit] won't likely need the entire event_nodes_by_id - too
   much info *)
module Context : sig
  (** [event_ctxt_by_id] holds EventCtxt.t for the events visible in the current
      scope

      [event_ids_by_uid] holds a mapping of event ids to corresponding uids for
      the events visible in the current scope

      [trigger_ctxt] the current scope's TriggerCtxt.t (holds a default value
      for the top-level)

      [event_participants_by_uid] (TODO probably remove)

      [event_nodes_by_uid] (global) previously collected information for every
      event node in the program (does not change)

      [dependencies] *)
  type t =
    { event_ctxt_by_id : EventCtxt.t Env.t
    ; event_ids_by_uid : event_id Env.t
    ; trigger_ctxt : TriggerCtxt.t
    ; event_participants_by_uid : CnfUserset.t
    ; event_nodes_by_uid : Verification.Typing.event_node StringMap.t
    ; dependencies : DependencyGraph.t
    }

  val init :
       CnfUserset.t
    -> Verification.Typing.event_node StringMap.t
    -> DependencyGraph.t
    -> t

  val initiator_of : event_id -> t -> CnfRole.t

  val receiver_of : event_id -> t -> CnfRole.t option

  val on_event : TriggerCtxt.t -> EventCtxt.t -> t -> t

  val find_event_ctxt_by_id : element_uid -> t -> EventCtxt.t

  val begin_spawn : event_id -> t -> t list

  val end_spawn : t -> t

  val to_string : t -> string
end = struct
  type t =
    { event_ctxt_by_id : EventCtxt.t Env.t
    ; event_ids_by_uid : event_id Env.t
    ; trigger_ctxt : TriggerCtxt.t
    ; event_participants_by_uid : CnfUserset.t
    ; event_nodes_by_uid : Verification.Typing.event_node StringMap.t
    ; dependencies : DependencyGraph.t
          (* ; decl_param_types_by_role : type_expr StringMap.t StringMap.t *)
    }

  let to_string t =
    let sprintf = Printf.sprintf in
    (* and scope_participants_str = participant_map_to_str t.participants_in_scope *)
    let event_ctxt_by_id =
      Env.to_string
        ~fmt:(EventCtxt.to_string ?indent:(Some " "))
        t.event_ctxt_by_id
    in
    sprintf "= dependency_graph:\n%s" (DependencyGraph.to_string t.dependencies)
    |> sprintf "= event_env:\n%s%s" event_ctxt_by_id
    |> sprintf
         "\n@projectability.ml [Context.t debug]\n= TriggerCtxt:\n %s\n%s"
         (TriggerCtxt.to_string t.trigger_ctxt)

  let init cnf_userset
      (event_nodes_by_uid : Verification.Typing.event_node StringMap.t)
      (dependencies : DependencyGraph.t) =
    (* let decl_param_types_by_role =
         StringMap.map (fun cnf_role -> cnf_role.CnfRole.param_types) cnf_userset
       in *)
    { event_ctxt_by_id = Env.empty
    ; event_ids_by_uid = Env.empty
    ; trigger_ctxt = TriggerCtxt.init cnf_userset
    ; event_participants_by_uid = CnfUserset.empty
    ; event_nodes_by_uid
    ; dependencies
    }

  let initiator_of event_id t =
    (* trusting that preprocessing has checked initiator/receiver args *)
    (TriggerCtxt.participants_of event_id t.trigger_ctxt).initiator

  let receiver_of event_id t =
    (* trusting that preprocessing has checked initiator/receiver args *)
    (TriggerCtxt.participants_of event_id t.trigger_ctxt).receiver

  let on_event trigger_ctxt event_ctxt t =
    let id = event_ctxt.EventCtxt.id
    and uid = event_ctxt.EventCtxt.uid in
    let event_ctxt_by_id =
      Env.bind event_ctxt.EventCtxt.id event_ctxt t.event_ctxt_by_id
    in
    let event_ids_by_uid = Env.bind uid id t.event_ids_by_uid in
    { t with event_ids_by_uid; event_ctxt_by_id; trigger_ctxt }

  let find_event_ctxt_by_id (event_uid : element_uid) (t : t) =
    Env.find_flat event_uid t.event_ctxt_by_id

  (* may lead to multiple scenarios depending on the initiator/receivers
     combinations - must check them all *)
  let begin_spawn event_id t =
    (* nested scope for nested events *)
    let event_ctxt_by_id = Env.begin_scope t.event_ctxt_by_id
    and event_ids_by_uid = Env.begin_scope t.event_ids_by_uid
    (* trusting that preprocessing checked spawn's source to be in scope *)
    and event_ctxt = Env.find_flat event_id t.event_ctxt_by_id in
    (* bindings defined in the trigger become available to trigger ctxt *)
    let bindings = event_ctxt.bindings in
    (* potentially multiple trigger ctxts reflecting distinct combinations
       of Initr/Recvr involved in the triggering event's execution;
       {@Initiator; @Receiver; sender & all_receivers} *)
    EventCtxt.resolve_trigger_participants event_ctxt
    |> List.map (fun (initiator, receiver, all) : TriggerCtxt.participants ->
           { initiator; receiver; all })
    |> List.map (fun participants ->
           TriggerCtxt.begin_scope event_id participants bindings t.trigger_ctxt)
    |> List.map (fun trigger_ctxt ->
           { t with trigger_ctxt; event_ctxt_by_id; event_ids_by_uid })

  let end_spawn (t : t) =
    let event_ctxt_by_id = Env.end_scope t.event_ctxt_by_id
    and event_ids_by_uid = Env.end_scope t.event_ids_by_uid
    and trigger_ctxt = TriggerCtxt.end_scope t.trigger_ctxt in
    { t with event_ctxt_by_id; event_ids_by_uid; trigger_ctxt }
end

(* event processing on "the way down" the recursion *)

(* verify that every param is assigned once *)
let rec verify_clash_free_assignment (constrained_roles : CnfUserset.t) =
  let bind_new sym assigned =
    if StringSet.mem sym assigned then
      Error [ (Nowhere, "Potentially conflicting assignment to " ^ sym) ]
    else Ok (StringSet.add sym assigned)
  in
  let verify_clash_free_assignment assigned = function
    | [] -> Ok assigned
    | [ Positive (CnfEq (sym, _)) ] -> bind_new sym assigned
    | [ Positive (CnfSymEq (sym1, sym2)) ] ->
      Result.bind (bind_new sym1 assigned) (fun assigned ->
          bind_new sym2 assigned)
    | _ -> Ok assigned
  in
  let verify_clash_free_role acc cnf_role =
    let { label; encoding; _ } : CnfRole.t = cnf_role in
    Result.map_error
      (fun err ->
        Error
          (( Nowhere
           , Printf.sprintf "TODO err-msg-fun clash assignemnt in role %s" label
           )
          :: err))
      (fold_left_error verify_clash_free_assignment StringSet.empty encoding)
    >>= fun _ -> Ok (StringMap.add label cnf_role acc)
  in
  StringMap.bindings constrained_roles
  |> List.map snd
  |> fold_left_error verify_clash_free_role StringMap.empty

(* verify that every param is assigned once *)
let rec filter_unique_assignments (constrained_roles : CnfUserset.t) =
  let bind_new sym assigned =
    if StringSet.mem sym assigned then
      Error [ (Nowhere, "Potentially conflicting assignment to " ^ sym) ]
    else Ok (StringSet.add sym assigned)
  in
  let rec verify_clash_free_assignment assigned = function
    | [] -> Ok assigned
    | [ Positive (CnfEq (sym, _)) ] -> bind_new sym assigned
    | [ Positive (CnfSymEq (sym1, sym2)) ] ->
      Result.bind (bind_new sym1 assigned) (fun assigned ->
          bind_new sym2 assigned)
    | _ -> Ok assigned
  in
  let rec verify_clash_free_role acc cnf_role =
    let { label; encoding; _ } : CnfRole.t = cnf_role in
    Result.map_error
      (fun err ->
        Error
          (( Nowhere
           , Printf.sprintf "TODO err-msg-fun clash assignemnt in role %s" label
           )
          :: err))
      (fold_left_error verify_clash_free_assignment StringSet.empty encoding)
    >>= fun _ -> Ok (StringMap.add label cnf_role acc)
  in
  StringMap.bindings constrained_roles
  |> List.map snd
  |> fold_left_error verify_clash_free_role StringMap.empty

(* TODO refactor - move to CnfRole *)
and is_user ({ param_types; encoding; _ } : CnfRole.t) =
  let binds_param param_sym = function
    | [ Positive (CnfSymEq (s1, s2)) ] ->
      s1 = param_sym
      && (not (Symbols.encodes_param_name s2))
      && not (Symbols.encodes_param_val_sym s2)
      || s2 = param_sym
         && (not (Symbols.encodes_param_name s1))
         && not (Symbols.encodes_param_val_sym s1)
    | [ Positive (CnfEq (s, _)) ] -> s = param_sym
    | _ -> false
  in
  List.for_all
    (fun param_sym -> List.exists (binds_param param_sym) encoding)
    (StringMap.bindings param_types
    |> List.map (fun x -> Symbols.encode_param_name @@ fst x))

and check_data_dependency (e0 : EventCtxt.t) (e1 : EventCtxt.t) =
  (* data dependency from e0 to e1 is valid iff every potential initiator of
      e0 (base) sees a single e1 (local/tx/rx), i.e., the dependency cannot be on
     a dual event; a tx/rx split would make the reference ambiguous (should
     probably be done within a spawn) *)
  let e0_base_init = EventCtxt.base_initiators e0
  and e1_base_init = EventCtxt.base_initiators e1
  and e1_base_rcv = EventCtxt.base_receivers e1
  and e1_base_participants = EventCtxt.base_participants e1 in
  (* 1. every potential initiator of e0 must participate in e1 *)
  if not @@ CnfUserset.is_subset e0_base_init e1_base_participants then
    let err_msg = err_msg_on_direct_dependency_may_not_be_visibile e0 e1 in
    Error [ (e0.event'.loc, err_msg) ]
    (* no initiator of e0 may "see" e1 as a dual event *)
  else
    let duals =
      StringMap.filter
        (fun _ v -> not @@ is_user v)
        (CnfUserset.resolve_intersection e1_base_init e1_base_rcv)
      |> CnfUserset.resolve_intersection e0_base_init
    in
    if not @@ CnfUserset.is_empty duals then
      let err_msg = on_err_ambiguous_data_dependency e0 e1 in
      Error [ (e0.event'.loc, err_msg) ]
    else Ok e0
(* process events and run pre-checks on "scope visibility" and data dependencies
   (so called, direct dependencies are checked on the recursion's way back up) *)
and process_events (ctxt : Context.t) (events : Choreo.event' list) =
  let open Verification.Preprocessing in
  (* encode event and update context accordingly *)
  let rec process_event (ctxt : Context.t) (event' : Choreo.event') =
    (* collect user-set expressions *)
    let uid = Option.get !(event'.uid)
    and id = (fst event'.data.info.data).data in
    let initiator, receivers =
      event'.data.participants.data |> function
      | Choreo.Local initr' -> (initr', [])
      | Choreo.Interaction (initr', recvrs) -> (initr', recvrs)
    in
    let trigger_ctxt, event_ctxt =
      EventCtxt.init
        event'
        ctxt.Context.trigger_ctxt
        ~uid
        ~id
        ~initiator
        ~receivers
    in
    let ctxt = Context.on_event trigger_ctxt event_ctxt ctxt in
    (ctxt, event_ctxt)
  (* projectability check *)
  and check_event (ctxt : Context.t) (event' : Choreo.event') =
    let ctxt, event_ctxt = process_event ctxt event' in
    (* let event_id = event_ctxt.id in *)
    (* users "participating" in the current scope *)
    let participants_in_scope =
      TriggerCtxt.participants_in_scope ctxt.Context.trigger_ctxt
    (* event's "base" participants - all potential initiators and receivers *)
    and event_base_participants = EventCtxt.base_participants event_ctxt in
    if not @@ CnfUserset.is_subset event_base_participants participants_in_scope
    then (
      (* not all of the event's "base" participants are in scope (visible) *)
      (* TODO [low priority] can further analyse the participants to convey
         a more precise indication of the error - which role(s)? *)
      print_endline "\n\n  !FAIL [event participants not in scope]\n\n";
      Error
        [ ( Nowhere
          , "TODO [extract err-msg-fun] some of the event's participants are \
             not in scope" )
        ])
    else
      (* TODO only collecting value-based data dependencies for now - not yet
         sure how to constrain the program to handle event-type dependencies *)
      (* !! DO NOT discard the following block - see comment in duplicate below *)
      (*  *)
      (* let _uid = event_ctxt.uid in
       let data_dependencies =
        (StringMap.find uid ctxt.event_nodes_by_uid).data_dependency
        |> ( function
        | Some (ValueDependency deps) ->
          (* reminder: deps are in terms of uid *)
          (* StringSet.iter (print_endline) deps; *)
          StringSet.to_list deps
        | _ -> [] )
        |> List.map (fun uid -> Env.find_flat uid ctxt.event_ids_by_uid)
        |> List.map (fun id -> Env.find_flat id ctxt.event_ctxt_by_id)
      in *)
      (*  *)
      (* OBSERVATION temporary override of data_dependencies as they should be
      TODO eventually remove collect_event_dependencies and rely on 
      preprocessing *)
      let data_dependencies = collect_event_dependencies ctxt event' in
      fold_left_error check_data_dependency event_ctxt data_dependencies
      >>= fun _ -> Ok ctxt
  in
  fold_left_error check_event ctxt events

and check_relations (ctxt : Context.t) (relations : Choreo.relation' list) =
  (* check a single dependency, no transitivity: ensure "at least one initiator
     observing both events" (relaxed version of "every initiator in
     participants") *)
  let rec check_plain_dependency ~src_id ~tgt_id ~rel_type =
    (* TODO take care of self-incident relations *)
    let src_ctxt = Context.find_event_ctxt_by_id src_id ctxt
    and tgt_ctxt = Context.find_event_ctxt_by_id tgt_id ctxt in
    let src_base_participants = EventCtxt.base_participants src_ctxt in
    let tgt_base_initiators = EventCtxt.base_initiators tgt_ctxt in
    let observers =
      CnfUserset.resolve_intersection src_base_participants tgt_base_initiators
    in
    if CnfUserset.is_empty observers then (
      (* TODO result.error *)
      print_endline "\n\n  !FAIL [redundant relation - applicable nowhere]\n\n";
      assert false)
    else
      (* TODO [under revising] *)
      match rel_type with
      | Milestone | Condition -> Ok ()
      | _ -> Ok ()
  (* e0 --> e1 --> e2 *)
  and check_transitive_dependency ~r1 ~r2 =
    (* initiators of e2 that observe e1, must also observe e0 *)
    let e0_ctxt = Context.find_event_ctxt_by_id r1.src_id ctxt
    and e1_ctxt = Context.find_event_ctxt_by_id r2.src_id ctxt
    and e2_ctxt = Context.find_event_ctxt_by_id r2.tgt_id ctxt in
    let e0_base_participants = EventCtxt.base_participants e0_ctxt
    and e1_base_init = EventCtxt.base_initiators e1_ctxt
    and e1_base_participants = EventCtxt.base_participants e1_ctxt
    and e2_base_init = EventCtxt.base_participants e2_ctxt in
    let observer_set =
      CnfUserset.resolve_intersection e2_base_init e1_base_participants
    in
    (* @pre: at least one observer of e1 in initiators of e2; e1-->e2 should 
     not have checked otherwise *)
    assert (not @@ CnfUserset.is_empty observer_set);
    if not @@ CnfUserset.is_subset observer_set e0_base_participants then (
      (* TODO result.error *)
      print_endline
        "\n\n  !FAIL [initiators of e2 observing e1 must also observe e0]\n\n";
      assert false)
    else if not @@ CnfUserset.is_subset e1_base_init e0_base_participants then (
      (* TODO result.error *)
      print_endline "\n\n  !FAIL [every initiator of e1 must observe  e0]\n\n";
      assert false)
    else Ok ()
  (* Process ctrl-flow relations exclusively, updating the runnning
    dependency graph to reflect each such relation.
    Called on the recursion's way down, where spawns must be processed
    according to this view. *)
  and process_ctrl_flow_rels (ctxt : Context.t) = function
    | ControlRelation (src_id', _expr', tgt_id', rel_type') as _rel ->
      let src_id, tgt_id, rel_type =
        (src_id'.data, tgt_id'.data, rel_type'.data)
      in
      let rel_t = { src_id; tgt_id; rel_type }
      and dependencies =
        DependencyGraph.on_ctrl_flow_rel_
          { src_id; tgt_id; rel_type }
          ctxt.dependencies
      in
      let _ = check_plain_dependency ~src_id ~tgt_id ~rel_type in
      (* we can check relations as they appear *)
      (* 1. check relation itself - based on src-tgt EventCtxt.t *)
      (* TODO *)
      (* 2. check chained direct-dependencies *)
      let _ =
        match rel_type with
        | Include | Exclude | Response ->
          let state_based_deps =
            DependencyGraph.outbound_state_based_deps
              ~exec_based_rel:rel_t
              dependencies
          and r1 = rel_t in
          iter_left_error
            (fun r2 -> check_transitive_dependency ~r1 ~r2)
            state_based_deps
          >>= fun () -> Ok ctxt
        | Condition | Milestone ->
          let exec_based_deps =
            DependencyGraph.inbound_exec_based_deps
              ~state_based_rel:rel_t
              dependencies
          and r2 = rel_t in
          iter_left_error
            (fun r1 -> check_transitive_dependency ~r1 ~r2)
            exec_based_deps
          >>= fun () -> Ok ctxt
      in
      Ok { ctxt with dependencies }
    | _ -> Ok ctxt
  (* Process spawn relations exclusively, triggering the projectability-check
     of the implicit spawn programs. *)
  and process_spawn_rels (ctxt : Context.t) = function
    | SpawnRelation (src_id', _, _expr', spawn_program) ->
      (* print_endline "\n\n  spawn \n\n"; *)
      let ctxts = Context.begin_spawn src_id'.data ctxt in
      iter_left_error (check_spawn_program spawn_program) ctxts
    | _ -> Ok ()
  in
  let relations = deannotate_list relations in
  (* Process all ctrl-flow relations before spawn relations;
      [ctxt] is updated in the first stage to reflect the ctrl-flow relations
      present in this scope *)
  fold_left_error process_ctrl_flow_rels ctxt relations >>= fun ctxt ->
  iter_left_error (process_spawn_rels ctxt) relations

and check_spawn_program (spawn_program : Choreo.spawn_program)
    (ctxt : Context.t) : (unit, (loc * role_label) list) result =
  process_events ctxt spawn_program.events >>= fun ctxt ->
  (* print_endline @@ Context.to_string ctxt; Ok () *)
  check_relations ctxt spawn_program.relations

(* ========================================================================= *)
(* ============================= temporary ================================= *)
(* TODO dependencies should be obtained upstream, from preprocessing - needs
 some work, delaying it for now... *)

(* collect direct dependencies (refs) on other events: requires processing
   the event's security level, data expression and participants *)
and collect_event_dependencies (ctxt : Context.t) (event' : event') =
  (* collect any event references within the security level *)
  let collect_sec_level_dependencies =
    (* collect event references within a single security label's parameter *)
    let collect_param_deps acc sec_label_param' =
      let _, param = sec_label_param'.data in
      match param.data with
      | Parameterised expr' -> collect_expr_dependencies expr' @ acc
      | _ -> acc
    in
    (* collect dependencies within a security label *)
    let collect_label_deps acc sec_label' =
      begin
        match sec_label'.data with
        | Sec sec ->
          let _, params = sec.data in
          List.fold_left collect_param_deps acc params
        | SecExpr expr' -> collect_expr_dependencies expr' @ acc
      end
    in
    List.fold_left collect_label_deps [] event'.data.security_level.data
  in
  let uniq l = List.sort_uniq String.compare l in
  collect_sec_level_dependencies |> fun sec_deps ->
  match event'.data.data_expr.data with
  | Input _ ->
    uniq sec_deps
    |> List.map (fun id -> Env.find_flat id ctxt.Context.event_ctxt_by_id)
  | Computation expr' ->
    collect_expr_dependencies expr'
    |> (fun expr_deps -> uniq (sec_deps @ expr_deps))
    |> List.map (fun id -> Env.find_flat id ctxt.Context.event_ctxt_by_id)

(** Collect EventId- and Trigger-related dependencies; checks whether all
    references (both trigger and event ids) are valid *)
and collect_expr_dependencies (expr' : expr') =
  let rec collect_deps acc exprs =
    match exprs with
    | [] -> List.sort_uniq String.compare acc
    | expr :: rest -> begin
      match expr.data with
      | EventRef id' -> collect_deps (id'.data :: acc) rest
      | Trigger _ -> collect_deps acc rest
      | PropDeref (expr, _) -> collect_deps acc (expr :: rest)
      | Record fields ->
        let values = List.map (fun { data = _, value; _ } -> value) fields in
        collect_deps acc (values @ rest)
      | BinaryOp (e1, e2, _) -> collect_deps acc (e1 :: e2 :: rest)
      | UnaryOp (e1, _) -> collect_deps acc (e1 :: rest)
      | _ -> collect_deps acc rest
    end
  in
  collect_deps [] [ expr' ]

and err_msg_on_direct_dependency_may_not_be_visibile (src : EventCtxt.t)
    (target : EventCtxt.t) =
  Printf.sprintf
    "[Projectability-check failed]\n\
    \  Event '%s' (%s) has a data-dependency on event '%s' (%s), but not every \
     potential initiator of '%s' is guaranteed to see '%s'\n\
    \    (suggestion: ensure that every initiator of '%s' participates in \
     '%s')."
    src.id
    (string_of_loc src.event'.loc)
    target.id
    (string_of_loc target.event'.loc)
    src.id
    target.id
    src.id
    target.id

and on_err_ambiguous_data_dependency (src : EventCtxt.t) (target : EventCtxt.t)
    =
  Printf.sprintf
    "%s\n\
    \  At least one initiator of event '%s' (%s) sees event '%s' (%s) as a \
     dual event, making the data-dependency ambiguous.\n\
    \    (suggestion: consider using a spawn instead)."
    err_t_ambiguous_dep_on_dual_event
    src.id
    (string_of_loc src.event'.loc)
    target.id
    (string_of_loc target.event'.loc)

(* ========================================================================= *)
(* ========================================================================= *)

(* entry-point *)
let check (program : Choreo.program)
    (typecheck_res : Verification.Typing.typecheck_result) =
  let top_level_userset = CnfUserset.of_role_decls program.roles in
  let dependency_graph = DependencyGraph.empty in
  let ctxt =
    Context.init
      top_level_userset
      typecheck_res.event_nodes_by_uid
      dependency_graph
  in
  check_spawn_program program.spawn_program ctxt
