(* open Syntax
open Tardis.Syntax
open Utils.Result
open Utils.Env

(**
  [translate [(role1, [(events1, relations1); ...; (eventsN, relationsN)]);...; (roleN, [(events1, relations1); ...; (eventsN, relationsN)])]]
  translates a list of pairs containing its [role_name] and its events and relations into a list of Babel contexts with the role name as key.
*)
let rec translate projection_list = 
  let projection_context = empty_projection_context in
  let projection_context = List.fold_left translate_projection projection_context projection_list in
  projection_context

(**
  [translate_projection projection_context (role, [(events1, relations1); ...; (eventsN, relationsN)])]
  translates a projection program into the [projection_context].
*)
and translate_projection projection_context projection = 
  let (role, (events, relations)) = projection in
  let context = translate_graph empty_context events relations in 
  let projection_context = (role, context) :: projection_context in
  projection_context

(**
  [translate_graph context [e1; ...; eN] [r1; ...; rN]]
  translates the graph from [events] and [relations], putting its result into the [context].
*)
and translate_graph context events relations  = 
  let context = translate_events context events in
  let context = translate_relations context relations in
  context

(**
  [translate_events context [e1; ...; eN]]
  translates each event from [e1; ...; eN] and puts the result into the [context].
*)
and translate_events context events = 
  List.fold_left translate_event context events 

(**
  [translate_event context event]
  translate the event [event] and puts the result into the [context].
*)
and translate_event context event = 
  let event' = event in
  let (id, label) = event'.info_proj in
  let io = event'.io_proj in
  let kind = event'.kind_proj in
  let class' = get_event_class io kind in
  let marking' = event'.marking_proj in
  let value = {
    event_id = id.data;
    event_label = label.data;
    event_class = class';
    event_marking = {
      included = marking'.included.data;
      pending = marking'.pending.data;
      executed = marking'.executed.data;
    };
  } in 
  let env = bind id.data value context.env in
  { context with env; events = value :: context.events }

(**
  [translate_relations context [r1; ...; rN]]
  translates each relation from [r1; ...; rN] and puts the result into the [context].
*)
and translate_relations context relations  =
  List.fold_left translate_relation context relations

(**
  [translate_relation_type rt]
  translates a relation type [rt] from Tardis to Babel.
*)
and translate_relation_type relation_type =
  let module TardisSy = Tardis.Syntax in
  let module BabelSy = Syntax in
  match relation_type with
  | TardisSy.Condition -> BabelSy.Condition
  | TardisSy.Include -> BabelSy.Include
  | TardisSy.Exclude -> BabelSy.Exclude
  | TardisSy.Milestone -> BabelSy.Milestone
  | TardisSy.Response -> BabelSy.Response

and get_event_class io kind = 
  let module TardisSy = Tardis.Syntax in
  let module BabelSy = Syntax in
  match io, kind with 

  | TardisSy.Input ty, TardisSy.InputAction init -> 
    BabelSy.InputAction (translate_type_expr ty.data, init.data)

  | TardisSy.Computation expr, TardisSy.OutputAction init -> 
    begin match !(expr.ty) with 
    (* Expecting type value in the annotation  *)
    | None -> BabelSy.OutputAction (translate_expr expr.data, BabelSy.UnitType, init.data)
    | Some ty -> BabelSy.OutputAction (translate_expr expr.data, translate_type_expr ty, init.data)
    end

  | TardisSy.Input ty, TardisSy.InputSend (init, receivers) -> 
    BabelSy.InputSendOperation (translate_type_expr ty.data, init.data, List.map deannotate receivers)

  | TardisSy.Computation expr, TardisSy.OutputSend (init, receivers) ->
    begin match !(expr.ty) with
    (* Expecting type value in the annotation  *)
    | None -> BabelSy.OutputSendOperation (translate_expr expr.data, BabelSy.UnitType, init.data, List.map deannotate receivers)
    | Some ty -> BabelSy.OutputSendOperation (translate_expr expr.data, translate_type_expr ty, init.data, List.map deannotate receivers)
    end

  | TardisSy.Input ty, TardisSy.Receive (init, receiver) -> 
    BabelSy.ReceiveOperation (translate_type_expr ty.data, init.data, receiver.data)

  | TardisSy.Computation expr, TardisSy.Receive (init, receiver) ->
    begin match !(expr.ty) with
    (* Expecting type value in the annotation  *)
    | None -> BabelSy.ReceiveOperation (BabelSy.UnitType, init.data, receiver.data)
    | Some ty -> BabelSy.ReceiveOperation (translate_type_expr ty, init.data, receiver.data)
    end

  | _ -> failwith "Not supported"



(**
  [translate_relation context rel]
  translates a relation [rel] and puts the result into the [context].
*)
and translate_relation context relation  = 
  let relation_value = 
    match relation with
    | SpawnRelation _ -> failwith "Spawn not supported"
    | ControlRelation (ev1, _, ev2, rel_ty) -> 
      let relation_type = translate_relation_type rel_ty in
      let ev_id1 = (fst (get ev1.data context.env)).event_id in
      let ev_id2 = (fst (get ev2.data context.env)).event_id in
      (relation_type, ev_id1, ev_id2)
  in
  { context with relations = relation_value :: context.relations }

(**
  [translate_expr expr']
  translates an non-annotated expression [expr'] from Tardis syntax into an expression in the Babel Syntax.
*)
and translate_expr expr'  = 
  let module TardisSy = Tardis.Syntax in
  let module BabelSy = Syntax in
  match expr' with
  | TardisSy.True -> BabelSy.Boolean true
  | TardisSy.False -> BabelSy.Boolean false
  | TardisSy.IntLit i -> BabelSy.Integer i
  | TardisSy.StringLit s -> BabelSy.String s
  | TardisSy.Parenthesized e -> BabelSy.ParenthesisExp (translate_expr e.data)
  | TardisSy.BinaryOp (e1, e2, Add) -> BabelSy.BinaryOp (translate_expr e1.data, translate_expr e2.data, Add)
  | TardisSy.BinaryOp (e1, e2, Mult) -> BabelSy.BinaryOp (translate_expr e1.data, translate_expr e2.data, Mult)
  | TardisSy.BinaryOp (e1, e2, Eq) -> BabelSy.BinaryOp (translate_expr e1.data, translate_expr e2.data, Eq)
  | TardisSy.BinaryOp (e1, e2, NotEq) -> BabelSy.BinaryOp (translate_expr e1.data, translate_expr e2.data, NotEq)
  | TardisSy.BinaryOp (e1, e2, GreaterThan) -> BabelSy.BinaryOp (translate_expr e1.data, translate_expr e2.data, GreaterThan)
  | TardisSy.BinaryOp (e1, e2, LessThan) -> BabelSy.BinaryOp (translate_expr e1.data, translate_expr e2.data, LessThan)
  | TardisSy.BinaryOp (e1, e2, And) -> BabelSy.BinaryOp (translate_expr e1.data, translate_expr e2.data, And)
  | TardisSy.BinaryOp (e1, e2, Or) -> BabelSy.BinaryOp (translate_expr e1.data, translate_expr e2.data, Or)
  | TardisSy.UnaryOp (e1, Minus) -> BabelSy.UnaryOp (translate_expr e1.data, Minus)
  | TardisSy.UnaryOp (e1, Negation) -> BabelSy.UnaryOp (translate_expr e1.data, Negation)
  | TardisSy.Identifier { data=id; _ } -> BabelSy.Identifier id
  | TardisSy.Trigger -> BabelSy.Trigger
  | TardisSy.PropDeref (e, p) -> BabelSy.PropDeref (translate_expr e.data, p.data)
  | TardisSy.List (es) -> BabelSy.List (List.map (fun e -> translate_expr e.data) es)
  | TardisSy.Record (ps) -> BabelSy.Record (List.map (fun (p, e) -> {field_name=p.data; field_value=translate_expr e.data}) ps)

(**
  [translate_type_expr type_expr']
  translates a type expression [type_expr'] from Tardis syntax into a type expression in the Babel Syntax.
*)
and translate_type_expr type_expr'  = 
  let module TardisSy = Tardis.Syntax in
  let module BabelSy = Syntax in
  match type_expr' with
  | TardisSy.StringTy -> BabelSy.StringType
  | TardisSy.IntTy -> BabelSy.IntType
  | TardisSy.BoolTy -> BabelSy.BoolType
  | TardisSy.UnitTy -> BabelSy.UnitType
  | TardisSy.RecordTy ps -> BabelSy.RecordType (List.map (fun (p, t) -> {field_name=p.data; field_ty=translate_type_expr t.data}) ps)
  (* FIXME: Add this types with failwith later!*)
  | TardisSy.ListTy t -> failwith "List type not supported"
  | TardisSy.ListTyEmpty -> failwith "List type not supported"
  | TardisSy.EventTy ev -> failwith "Event type not supported" *)
