module Choreo = Frontend.Syntax
open Choreo
open Sat
open Utils

(* open Utils.Env *)
open Utils.Results
open Utils.Logs
open Frontend.Unparser

exception Typecheck_IFC_error of string

module TreeMap = Map.Make (String)

type ('a, 'b) leakError =
  | SAT
  | Unknown of 'a
  | UNSAT of 'b

type node =
  { info : event_info'
  ; security_list : security_level
  ; io : data_expr
  ; kind : participants'
  ; env : node Env.t
  }

(* =========================================================================
   ==================== DEBUG section (temporary: to remove) =============== *)

let debug_SCs id list =
  print_endline "====== [DEBUG start] SCs ===";
  print_endline @@ id ^ " : " ^ unparse_security_level' list;
  print_endline "====== [DEBUG end] SCs ==="

let unparse_level_t (level : node) =
  let id, label = level.info.data in
  id.data ^ " : " ^ label.data ^ " : "
  ^ unparse_security_level' level.security_list

let debug_env (env : node Env.t) =
  let open Printf in
  let rec debug_aux env =
    match env with
    | [] -> print_endline "< end of level >\n"
    | (s, level) :: xs ->
      print_endline @@ s ^ " : " ^ unparse_level_t level;
      debug_aux xs
  in
  print_endline "\n ====== [DEBUG start] Env ===\n";
  List.iter (fun scope -> debug_aux scope) env;
  print_endline " ====== [DEBUG end] Env ===\n"

let debug_lattice (map : string list TreeMap.t) =
  let open Printf in
  print_endline " ====== [DEBUG start] Lattice ===";
  TreeMap.iter
    (fun key value ->
      print_endline @@ " From: " ^ key ^ " to: " ^ String.concat ", " @@ value)
    map;
  print_endline " ====== [DEBUG end] Lattice ==="

(* =========================================================================
   ========================== END of DEBUG section ========================= *)

let _TRIGGER : string = "@trigger"

let _CONSTANT_VALUE : string = "value"

let _BOT : string = "Bot"

let _TOP : string = "Top"

let _BOT_LEVEL : security_level = [ annotate (annotate _BOT, []) ]

let global_label_SC : security_level TreeMap.t ref = ref TreeMap.empty

module CnfExprCtxt : sig
  type t =
    { symbolic : expr' Env.t
    ; contraints : cnf_formula TreeMap.t
    }

  val and_list :
       (cnf_formula, (loc * element_uid) list) leakError list
    -> (cnf_formula, (loc * element_uid) list) leakError

  val or_list :
       (cnf_formula, (loc * element_uid) list) leakError list
    -> (cnf_formula, (loc * element_uid) list) leakError

  val begin_scope : t -> t

  val end_scope : t -> t

  val empty : t

  val return_constainsts : t -> cnf_formula TreeMap.t

  val update_cnf_formula : string -> cnf_formula -> t -> t
end = struct
  type t =
    { symbolic : expr' Env.t (* string -> Expr ( stringfy da expr -> expr')*)
    ; contraints : cnf_formula TreeMap.t (* string -> cnf ( uuid event -> cnf)*)
    }

  let and_list (lst : (cnf_formula, (loc * element_uid) list) leakError list) :
      (cnf_formula, (loc * element_uid) list) leakError =
    let rec aux lst acc =
      match lst with
      | [] -> acc
      | x :: xs -> (
        match x with
        | UNSAT s -> UNSAT s
        | Unknown s -> (
          match acc with
          | Unknown s' ->
            let p : cnf_formula = cnf_and s s' in
            aux xs (Unknown p)
          | _ -> aux xs (Unknown s))
        | SAT -> aux xs acc)
    in
    aux lst SAT

  let or_list (lst : (cnf_formula, (loc * element_uid) list) leakError list) :
      (cnf_formula, (loc * element_uid) list) leakError =
    let rec aux lst acc =
      match lst with
      | [] -> acc
      | x :: xs -> (
        match x with
        | UNSAT s -> (
          match acc with
          | UNSAT s' ->
            aux xs (UNSAT (s @ s'))
          | _ -> aux xs acc)
        | Unknown s -> (
          match acc with
          | Unknown s' ->
            let p : cnf_formula = cnf_or s s' in
            aux xs (Unknown p)
          | UNSAT _ ->
            Unknown s
          | SAT -> aux xs acc)
        | SAT -> SAT)
    in
    aux lst (UNSAT [ (Nowhere, "Error in or_list") ])

  let empty : t = { symbolic = Env.empty; contraints = TreeMap.empty }

  let begin_scope ctxt =
    { symbolic = Env.begin_scope ctxt.symbolic; contraints = ctxt.contraints }

  let end_scope ctxt =
    { symbolic = Env.end_scope ctxt.symbolic; contraints = ctxt.contraints }

  let update_cnf_formula (uuid : string) (cnf : cnf_formula) ctxt =
    let new_cnf =
      match TreeMap.find_opt uuid ctxt.contraints with
      | None -> cnf
      | Some cnf' -> cnf_and cnf cnf'
    in
    match cnf_sat_solve new_cnf with
    | None -> ctxt
    | Some solver_cnf ->
      { symbolic = ctxt.symbolic
      ; contraints = TreeMap.add uuid solver_cnf ctxt.contraints
      }
  (* let cnf_expr ctxt =
     let rec aux (env : node Env.t) =
       match env with
       | [] -> TreeMap.empty
       | (s, node) :: xs ->
         let new_map = aux xs in
         TreeMap.add s (node.io, node.security_list) new_map
     in
     aux ctxt.symbolic *)

  let return_constainsts ctxt = ctxt.contraints
end

module Ctxt : sig
  open Utils

  type t =
    { env : node Env.t
    ; lattice : string list TreeMap.t ref
    ; sec_params : string list TreeMap.t ref
    ; symbolic : CnfExprCtxt.t
    ; global_label_SC : security_level TreeMap.t ref
    ; trigger_stack : string list
    }

  val begin_scope : role_label -> t -> t

  val end_scope : t -> t

  val create_and_bind_node : role_label -> event -> t -> t

  val bind : role_label -> node -> t -> t

  val reset_references : t -> (cnf_formula TreeMap.t, 'b) result

  val get_trigger : t -> string

  val add_symbol :
       'a annotated
    -> cnf_formula
    -> string
    -> t
    -> (t, (loc * string) list) result

  val find_env :
    int -> t -> (node Env.t * node Env.t, (loc * string) list) result
end = struct
  open Utils

  type t =
    { env : node Env.t
    ; lattice : string list TreeMap.t ref
    ; sec_params : string list TreeMap.t ref
    ; symbolic : CnfExprCtxt.t
    ; global_label_SC : security_level TreeMap.t ref
    ; trigger_stack : string list
    }

  let get_trigger ctxt = List.hd ctxt.trigger_stack

  let reset_references ctxt =
    global_label_SC := TreeMap.empty;
    Ok ctxt.symbolic.contraints

  let begin_scope trigger ctxt =
    { env = Env.begin_scope ctxt.env
    ; lattice = ctxt.lattice
    ; sec_params = ctxt.sec_params
    ; symbolic = CnfExprCtxt.begin_scope ctxt.symbolic
    ; global_label_SC = ctxt.global_label_SC
    ; trigger_stack = trigger :: ctxt.trigger_stack
    }

  let end_scope ctxt =
    { env = Env.end_scope ctxt.env
    ; lattice = ctxt.lattice
    ; sec_params = ctxt.sec_params
    ; symbolic = CnfExprCtxt.end_scope ctxt.symbolic
    ; global_label_SC = ctxt.global_label_SC
    ; trigger_stack = List.tl ctxt.trigger_stack
    }

  let add_symbol obj cnf error ctxt =
    begin
      match !(obj.uid) with
      | Some uuid ->
        Ok
          { ctxt with
            symbolic = CnfExprCtxt.update_cnf_formula uuid cnf ctxt.symbolic
          }
      | None -> Error [ (obj.loc, error) ]
    end

  let create_and_bind_node id node ctxt : t =
    let mkNodeEvent (event : event) env : node =
      { security_list = event.security_level.data
      ; io = event.data_expr.data
      ; info = event.info
      ; kind = event.participants
      ; env
      }
    in
    { ctxt with env = Env.bind id (mkNodeEvent node ctxt.env) ctxt.env }

  let bind id node ctxt : t = { ctxt with env = Env.bind id node ctxt.env }

  let find_env (depth : int) (ctxt : t) =
    let rec aux (env : node Env.t) (depth : int) =
      if depth = 0 then Ok env
      else if List.length env = 0 then Error [ (Nowhere, "Error in find_env") ]
      else aux (Env.end_scope env) (depth - 1)
    in
    match aux ctxt.env depth with
    | Ok new_env -> Ok (ctxt.env, new_env)
    | Error e -> Error e
end

module EvalExpr : sig
  type evalExpr =
    | Bool of bool
    | String of string
    | Int of int
    | Unknown
    | Error of (loc * string)

  val evalExpr : expr' -> node Env.t -> evalExpr
end = struct
  type evalExpr =
    | Bool of bool
    | String of string
    | Int of int
    | Unknown
    | Error of (loc * string)

  type ('a, 'b) resultExpr =
    | Ok of 'a
    | Error of 'b
    | Unknown

  let rec evalExpr expr env : evalExpr =
    match expr.data with
    | True -> Bool true
    | False -> Bool false
    | IntLit n -> Int n
    | StringLit s -> String s
    | Parenthesized exp -> evalExpr exp env
    | BinaryOp (exp1, exp2, op) -> (
      let v1 = evalExpr exp1 env in
      let v2 = evalExpr exp2 env in
      match (op, v1, v2) with
      | Add, Int n1, Int n2 -> Int (n1 + n2)
      | Add, String s1, String s2 -> String (s1 ^ s2)
      | Mult, Int n1, Int n2 -> Int (n1 * n2)
      | Eq, Int n1, Int n2 -> Bool (n1 = n2)
      | Eq, String s1, String s2 -> Bool (String.compare s1 s2 = 0)
      | Eq, Bool b1, Bool b2 -> Bool (b1 = b2)
      | NotEq, Int n1, Int n2 -> Bool (n1 <> n2)
      | NotEq, String s1, String s2 -> Bool (String.compare s1 s2 <> 0)
      | NotEq, Bool b1, Bool b2 -> Bool (b1 <> b2)
      | GreaterThan, Int n1, Int n2 -> Bool (n1 > n2)
      | LessThan, Int n1, Int n2 -> Bool (n1 < n2)
      | And, Bool b1, Bool b2 -> Bool (b1 && b2)
      | Or, Bool b1, Bool b2 -> Bool (b1 || b2)
      | _ -> failwith "Invalid binary operation")
    | UnaryOp (exp, op) -> (
      match (op, evalExpr exp env) with
      | Minus, Int n -> Int (-n)
      | Negation, Bool b -> Bool (not b)
      | _ -> failwith "Invalid unary operation")
    | PropDeref (e, prop) -> (
      let rec evalProp e prop env : ('a, 'b) resultExpr =
        match e.data with
        | Trigger t -> (
          match Env.find_flat_opt t env with
          | None -> Error (e.loc, "Trigger Event does not exist")
          | Some node -> (
            match node.io with
            | Input _ -> Unknown
            | Computation expr -> Ok (expr, node.env)))
        | EventRef e -> (
          match Env.find_flat_opt e.data env with
          | None -> Error (e.loc, "Event does not exist")
          | Some node -> (
            match node.io with
            | Input _ -> assert false
            | Computation expr -> Ok (expr, node.env)))
        | PropDeref (e, prop2) -> (
          match evalProp e prop2 env with
          | Ok (exp, env2) -> (
            match exp.data with
            | Record rs -> (
              match
                List.find_opt
                  (fun x ->
                    let key, _ = x.data in
                    let p = String.equal key.data prop.data in
                    p)
                  rs
              with
              | None -> Error (e.loc, "Error in propDeref not found record")
              | Some s ->
                let r, expr = s.data in
                Ok (expr, env2))
            | _ -> Ok (expr, env2))
          | Unknown -> Unknown
          | Error err -> Error (fst err, "Error in propDeref " ^ "\n" ^ snd err)
          )
        | _ -> Error (e.loc, "Invalid property dereference")
      in
      match evalProp e prop env with
      | Ok (expr, env2) -> evalExpr expr env2
      | Unknown -> Unknown
      | Error s -> Error s)
    | _ -> failwith "Unhandled expression case: "
end

let rec check_static_information_security program =
  let ctxt : Ctxt.t =
    { env = Env.empty
    ; lattice = ref TreeMap.empty
    ; sec_params = ref TreeMap.empty
    ; symbolic = CnfExprCtxt.empty
    ; global_label_SC = ref TreeMap.empty
    ; trigger_stack = []
    }
  in
  build_lattice program.roles program.security_lattice ctxt >>= fun ctxt ->
  retrive_security_of_events
    ctxt
    (program.spawn_program.events, program.spawn_program.relations)
  >>= fun ctxt ->
  check_security_graph
    ctxt
    (program.spawn_program.events, program.spawn_program.relations)
  >>= fun _ -> Ctxt.reset_references ctxt

and build_lattice (roles : value_dep_role_decl' list)
    (flw : flow_relation' list) (ctxt : Ctxt.t) =
  let build_lattice_level (ctxt : Ctxt.t) (flw : flow_relation') =
    (* (lattice : string list TreeMap.t ref) = *)
    let left, right = flw.data in
    match TreeMap.find_opt left.data !(ctxt.lattice) with
    | Some l ->
      ctxt.lattice := TreeMap.add left.data (right.data :: l) !(ctxt.lattice);
      Ok ctxt
    | None ->
      Error
        [ (left.loc, "Error in lattice flow " ^ left.data ^ " -> " ^ right.data)
        ]
  in

  ctxt.sec_params :=
    List.fold_left
      (fun acc level ->
        let label, params = level.data in
        let paramsLabel =
          List.map (fun (id, _) -> id.data) (deannotate_list params)
        in
        TreeMap.add label.data paramsLabel acc)
      !(ctxt.sec_params)
      roles;

  ctxt.lattice :=
    List.fold_left
      (fun acc label ->
        let label1, _ = label.data in
        TreeMap.add label1.data [] acc)
      !(ctxt.lattice)
      roles;

  fold_left_error build_lattice_level ctxt flw >>= fun ctxt ->
  let all_parents =
    TreeMap.fold (fun key _ acc -> key :: acc) !(ctxt.lattice) []
  in
  let all_children =
    TreeMap.fold (fun _ values acc -> values @ acc) !(ctxt.lattice) []
  in
  let is_leaf =
    List.filter (fun key -> not (List.mem key all_children)) all_parents
  in
  let is_root =
    List.filter (fun key -> not (List.mem key all_parents)) all_children
  in
  ctxt.lattice := TreeMap.add _BOT is_leaf !(ctxt.lattice);
  ctxt.lattice := TreeMap.add _TOP is_root !(ctxt.lattice);
  Ok ctxt

(** Function used to retrieve the security levels of all events in program. To
    be used in data of events. *)
and retrive_security_of_events (ctxt : Ctxt.t) (events, crs) =
  let process_events (ctxt : Ctxt.t) (event : event') =
    let all_levels_const (event_data : event) =
      let security_level = event_data.security_level.data in
      List.for_all
        (fun sec_label ->
          let id, param = sec_label.data in
          match param with
          | [] -> true
          | xs ->
            List.for_all
              (fun x ->
                match !(x.ty) with
                | None -> true
                | Some t -> t.is_const)
              xs)
        security_level
    in
    let event_data = event.data in
    let id, label = event_data.info.data in
    global_label_SC :=
      TreeMap.add label.data event_data.security_level.data !global_label_SC;

    if all_levels_const event_data then
      Ok (Ctxt.create_and_bind_node id.data event_data ctxt)
    else
      Error
        [ ( event.loc
          , "Error in typechecking security level of event " ^ id.data ^ ":"
            ^ label.data )
        ]
  in
  let process_spawn_relation (ctxt : Ctxt.t) cr =
    match cr.data with
    | ControlRelation _ -> Ok ctxt
    | SpawnRelation (_, trigger, _, prog) ->
      retrive_security_of_events
        (Ctxt.begin_scope trigger ctxt)
        (prog.events, prog.relations)
      >>= fun ctxt -> Ok (Ctxt.end_scope ctxt)
  in
  fold_left_error process_events ctxt events >>= fun ctxt2 ->
  fold_left_error process_spawn_relation ctxt2 crs

and get_security_of_expr (ctxt : Ctxt.t) expr =
  match expr.data with
  | True -> Ok _BOT_LEVEL
  | False -> Ok _BOT_LEVEL
  | IntLit _ -> Ok _BOT_LEVEL
  | StringLit _ -> Ok _BOT_LEVEL
  | Parenthesized expr -> get_security_of_expr ctxt expr
  | BinaryOp (e1, e2, _) -> (
    match get_security_of_expr ctxt e1 with
    | Error e -> Error ((e1.loc, "Error in exp node" ^ unparse_expr e1) :: e)
    | Ok pc1 -> (
      match get_security_of_expr ctxt e2 with
      | Error e -> Error ((e2.loc, "Error in exp node" ^ unparse_expr e2) :: e)
      | Ok pc2 -> Ok (get_levels_from_SC_List filter_higher_levels pc1 pc2 ctxt)
      ))
  | UnaryOp (e, _) -> get_security_of_expr ctxt e
  | EventRef id -> (
    match Env.find_flat_opt id.data ctxt.env with
    | None -> Error [ (id.loc, "Error in static check expr " ^ id.data) ]
    | Some node -> Ok node.security_list)
  | Trigger t -> (
    match Env.find_flat_opt t ctxt.env with
    | None -> Error [ (expr.loc, "Error in static check trigger " ^ t) ]
    | Some sec_node -> Ok sec_node.security_list)
  | PropDeref (expr, _) -> get_security_of_expr ctxt expr
  | List list ->
    let new_list = List.map (fun e -> get_security_of_expr ctxt e) list in
    concat_list new_list expr.loc ctxt
  | Record list ->
    let n_list =
      List.map (fun r -> get_security_of_expr ctxt (snd r.data)) list
    in
    concat_list n_list expr.loc ctxt

(** Check security levels of graph 1. Verify events 2. Verify relations *)
and check_security_graph (ctxt : Ctxt.t) (events, crs) =
  fold_left_error check_security_event ctxt events >>= fun ctxt1 ->
  fold_left_error check_security_relation ctxt1 crs >>= fun ctxt2 -> Ok ctxt2

and check_security_relation (ctxt : Ctxt.t)
    cr (*(env, lattice, sec_params, simbolic_env)*) =
  match cr.data with
  | ControlRelation (e1, exp, e2, _) -> (
    match get_security_of_expr ctxt exp with
    | Error e ->
      Error
        (( cr.loc
         , "Error in control relation checking event expression" ^ e1.data )
        :: e)
    | Ok security_level -> (
      match
        (Env.find_flat_opt e1.data ctxt.env, Env.find_flat_opt e2.data ctxt.env)
      with
      | None, _ ->
        Error
          [ ( cr.loc
            , "Error in control relation finding event1 in " ^ e1.data ^ "flows"
              ^ e2.data )
          ]
      | _, None ->
        Error
          [ ( cr.loc
            , "Error in control relation finding event2 in " ^ e1.data ^ "flows"
              ^ e2.data )
          ]
      | Some node1, Some node2 -> (
        let verify_relations_events (cond : cnf_formula) =
          match
            check_less_or_equal_security_level
              node1.security_list
              node1.env
              node2.security_list
              node2.env
              ctxt.sec_params
              ctxt.lattice
              true
          with
          | UNSAT e ->
            Error
              (( cr.loc
               , "Does not flow in control relation " ^ e1.data ^ "("
                 ^ unparse_security_level' node1.security_list
                 ^ ") -> " ^ e2.data ^ " ("
                 ^ unparse_security_level' node2.security_list
                 ^ ")" )
              :: e)
          | Unknown e ->
            Ctxt.add_symbol
              cr
              (cnf_and cond e)
              "Error in control relation: Invalid relation uuid in unknown"
              ctxt
          | SAT ->
            Ctxt.add_symbol
              cr
              cond
              "Error in control relation: Invalid relation uuid in SAT"
              ctxt
        in

        match
          check_less_or_equal_security_level
            node1.security_list
            node1.env
            security_level
            ctxt.env
            ctxt.sec_params
            ctxt.lattice
            false
        with
        | SAT -> verify_relations_events []
        | UNSAT e ->
          Error
            (( cr.loc
             , "Does not flow in control relation event to expression ("
               ^ unparse_security_level' node1.security_list
               ^ ") -> " ^ " ("
               ^ unparse_security_level' security_level
               ^ ")" )
            :: e)
        | Unknown e -> verify_relations_events e)))
  | SpawnRelation (event, trigger_label, exp, prog) -> (
    match get_security_of_expr ctxt exp with
    | Error err ->
      Error ((exp.loc, "Error in event expression " ^ event.data) :: err)
    | Ok security_list -> (
      match Env.find_flat_opt event.data ctxt.env with
      | None -> Error [ (cr.loc, "Error finding event: " ^ event.data) ]
      | Some node -> (
        let spawn_creation ctxt =
          let new_ctxt =
            Ctxt.begin_scope trigger_label ctxt |> Ctxt.bind trigger_label node
            (* Env.bind trigger_label node @@ Env.begin_scope ctxt.env *)
          in
          match check_security_graph new_ctxt (prog.events, prog.relations) with
          | Ok ctxt2 -> Ok (Ctxt.end_scope ctxt2)
          | Error s -> Error ((cr.loc, "Error in spawn relation") :: s)
        in
        match
          check_less_or_equal_security_level
            node.security_list
            node.env
            security_list
            ctxt.env
            ctxt.sec_params
            ctxt.lattice
            false
        with
        | UNSAT e ->
          Error
            (( exp.loc
             , "Error in event " ^ event.data ^ " expression "
               ^ unparse_expr exp ^ " in spawn" )
            :: e)
        | Unknown e -> begin
          match
            Ctxt.add_symbol
              cr
              e
              "Error in control relation: Invalid relation uuid in Spawn"
              ctxt
          with
          | Error e ->
            Error
              (( exp.loc
               , "Error in event " ^ event.data ^ " expression "
                 ^ unparse_expr exp ^ " in spawn" )
              :: e)
          | Ok ctxt2 -> spawn_creation ctxt2
        end
        | SAT -> spawn_creation ctxt)))

(*1. Compare levels of the event with the trigger, if there is no trigger true
  2. Compare levels of the event with the data 3. Check wellform *)
(* TODO: retornar num ponto comum o solve das expr*)
and check_security_event (ctxt : Ctxt.t) event =
  (* Find do  trigger resolver*)
  let check_security_trigger (event : event') (ctxt : Ctxt.t) =
    if ctxt.trigger_stack = [] then Ok []
    else
      let trigger_node = Env.find_flat (Ctxt.get_trigger ctxt) ctxt.env in
      match
        check_less_or_equal_security_level
          trigger_node.security_list
          trigger_node.env
          event.data.security_level.data
          ctxt.env
          ctxt.sec_params
          ctxt.lattice
          true
      with
      | UNSAT e ->
        Error ((event.loc, "Error in security with event and trigger") :: e)
      | SAT -> Ok []
      | Unknown e ->
        (* print_endline @@ unparse_cnf_formula e; *)
        Ok e
  in

  let static_check_security_of_data_expr event ctxt =
    let rec check_security_of_type_expr type_expr lattice params =
      match type_expr.data with
      | UnitTy -> Ok _BOT_LEVEL
      | StringTy -> Ok _BOT_LEVEL
      | IntTy -> Ok _BOT_LEVEL
      | BoolTy -> Ok _BOT_LEVEL
      | EventRefTy (s, _) -> (
        match TreeMap.find_opt s !global_label_SC with
        | None ->
          Error
            [ (type_expr.loc, "Error in static check Event type expr " ^ s) ]
        | Some node ->
          Ok (get_levels_from_SC_List filter_higher_levels node [] ctxt))
      | EventTy s -> (
        match TreeMap.find_opt s !global_label_SC with
        | Some node ->
          Ok (get_levels_from_SC_List filter_higher_levels node [] ctxt)
        | None ->
          Error
            [ (type_expr.loc, "Error in static check Event type expr " ^ s) ])
      | RecordTy r -> (
        let list_pc =
          List.fold_left
            (fun acc l ->
              match acc with
              | Error e -> Error ((type_expr.loc, "Error in RecordTy") :: e)
              | Ok acc' -> (
                match l with
                | Ok l' -> Ok (acc' @ l')
                | Error e -> Error e))
            (Ok [])
            (List.map
               (fun record ->
                 check_security_of_type_expr (snd record.data) lattice params)
               r)
        in
        match list_pc with
        | Error e -> Error e
        | Ok get_list ->
          Ok (get_levels_from_SC_List filter_higher_levels get_list [] ctxt))
      | ListTy _ ->
        Error [ (type_expr.loc, "Error in static check ListTy type expr ") ]
      | ListTyEmpty -> Ok _BOT_LEVEL
    in
    match event.data_expr.data with
    | Input ty_expr -> (
      match
        check_security_of_type_expr ty_expr ctxt.lattice !(ctxt.sec_params)
      with
      | Error e ->
        Error
          (( ty_expr.loc
           , "Error in expression of event " ^ (fst event.info.data).data ^ ":"
             ^ (snd event.info.data).data )
          :: e)
      | Ok security_lvl -> (
        match
          check_less_or_equal_security_level
            event.security_level.data
            ctxt.env
            security_lvl
            ctxt.env
            ctxt.sec_params
            ctxt.lattice
            false
        with
        | SAT -> Ok []
        | UNSAT e ->
          Error
            (( ty_expr.loc
             , "Error static ifc in expression of event "
               ^ (fst event.info.data).data ^ ":" ^ (snd event.info.data).data
             )
            :: e)
        | Unknown e -> Ok e))
    | Computation expr -> (
      match get_security_of_expr ctxt expr with
      | Error e ->
        Error
          (( expr.loc
           , "Error static ifc node exp " ^ (fst event.info.data).data ^ ":"
             ^ (snd event.info.data).data )
          :: e)
      | Ok security_level -> (
        match
          check_less_or_equal_security_level
            event.security_level.data
            ctxt.env
            security_level
            ctxt.env
            ctxt.sec_params
            ctxt.lattice
            false
        with
        | SAT -> Ok []
        | UNSAT e ->
          Error
            (( expr.loc
             , "Error static ifc in node exp " ^ (fst event.info.data).data
               ^ ":" ^ (snd event.info.data).data )
            :: e)
        | Unknown e -> Ok e))
  in

  let check_wellformedness _ = Ok [] in
  let static_checking_security_param (security_event : security_level) loc ctxt
      =
    fold_left_error
      (fun (acc, ctxt) (lvl : sec_label') ->
        let _, list_params1 = lvl.data in
        let list_params_expr =
          List.map (fun (_, exp) -> exp.data) (deannotate_list list_params1)
        in
        let list_params =
          List.map
            (fun exp ->
              match exp with
              | Top -> Ok _BOT_LEVEL
              | Bot -> Ok _BOT_LEVEL
              | Parameterised exp1 -> get_security_of_expr ctxt exp1)
            list_params_expr
        in
        match concat_list list_params loc ctxt with
        | Ok l -> Ok (l @ acc, ctxt)
        | Error e -> Error e)
      ([], ctxt)
      security_event
    >>= fun (sec2, ctxt2) ->
    Ok (get_levels_from_SC_List filter_higher_levels sec2 [] ctxt2)
  in

  let id, label = event.data.info.data in
  match check_security_trigger event ctxt with
  | Error e ->
    Error
      (( event.data.info.loc
       , "Error checking ifc trigger in event " ^ id.data ^ ":" ^ label.data )
      :: e)
  | Ok cnf_list -> (
    match static_check_security_of_data_expr event.data ctxt with
    | Error e ->
      Error
        (( event.data.info.loc
         , "Error checking ifc levels in event " ^ id.data ^ ":" ^ label.data )
        :: e)
    | Ok cnf_list2 -> (
      match check_wellformedness event with
      | Error e ->
        Error
          (( event.data.info.loc
           , "Error checking wellformedness in event " ^ id.data ^ ":"
             ^ label.data )
          :: e)
      | Ok cnf_list3 -> (
        let new_ctxt = Ctxt.create_and_bind_node id.data event.data ctxt in
        (* Env.bind id.data (mkNodeEvent event.data env) env *)
        (* let new_env = bind id.data (mkNodeEvent event.data env) env in *)
        (* TODO: retorna ctxt com o cnf and solver de tudo*)
        match
          static_checking_security_param
            event.data.security_level.data
            Nowhere
            new_ctxt
        with
        | Error e ->
          Error
            (( event.data.info.loc
             , "Error in static checking security param in event " ^ id.data
               ^ ":" ^ label.data )
            :: e)
        | Ok list -> (
          match
            check_less_or_equal_security_level
              event.data.security_level.data
              ctxt.env
              list
              ctxt.env
              ctxt.sec_params
              ctxt.lattice
              false
          with
          | SAT -> begin
            match
              Ctxt.add_symbol
                event
                (cnf_and (cnf_and cnf_list cnf_list2) cnf_list3)
                "Error in event: Invalid event uuid in SAT"
                new_ctxt
            with
            | Error e ->
              Error
                (( event.data.info.loc
                 , "Error in static checking security param in event " ^ id.data
                   ^ ":" ^ label.data )
                :: e)
            | Ok new_ctxt -> Ok new_ctxt
          end
          | UNSAT e ->
            Error
              (( event.data.info.loc
               , "Error in static checking security param in event " ^ id.data
                 ^ ":" ^ label.data )
              :: e)
          | Unknown e ->
            (* print_endline @@ unparse_cnf_formula e; *)
            begin
              match
                Ctxt.add_symbol
                  event
                  (cnf_and e (cnf_and (cnf_and cnf_list cnf_list2) cnf_list3))
                  "Error in event: Invalid event uuid in Unknown"
                  new_ctxt
              with
              | Error e ->
                Error
                  (( event.data.info.loc
                   , "Error in static checking security param in event "
                     ^ id.data ^ ":" ^ label.data )
                  :: e)
              | Ok new_ctxt -> Ok new_ctxt
            end))))

and check_less_or_equal_security_level (event_security : security_level)
    (env : node Env.t) (exp_security : security_level) (env2 : node Env.t)
    sec_params lattice relation =
  (* let debug_map_list (l : (cnf_formula, (loc * element_uid) list) leakError)
     = let open Printf in match l with | UNSAT _ -> print_endline "UNSAT" | SAT
     -> print_endline "SAT " | Unknown s -> unparse_cnf_formula s |>
     print_endline in *)
  let sat_list =
    List.map
      (fun node_2 ->
        let aux_list =
          List.map
            (fun node_1 ->
              if relation then
                depth_first_search node_1 node_2 !lattice [] sec_params env env2
              else
                let p =
                  depth_first_search
                    node_2
                    node_1
                    !lattice
                    []
                    sec_params
                    env2
                    env
                in
                p)
            event_security
        in
        CnfExprCtxt.or_list aux_list)
      exp_security
  in
  CnfExprCtxt.and_list sat_list

and depth_first_search (node1 : sec_label') (node2 : sec_label')
    (lattice : string list TreeMap.t) (visited : string list) params
    (env : node Env.t) env2 =
  if List.mem (fst node1.data).data visited then SAT
  else if (fst node1.data).data = (fst node2.data).data then
    compareSecurityLevels node1 node2 params env env2
  else
    let rec depth_first_search' (label1 : string) (label2 : string)
        (lattice : string list TreeMap.t) (visited : string list)
        (path : string list) =
      if List.mem label1 visited then SAT
      else if label1 = label2 then
        compareSecurityLevels
          (annotate (annotate label1, []))
          node2
          params
          env
          env2
      else
        match TreeMap.find_opt label1 lattice with
        | Some l ->
          CnfExprCtxt.or_list
            (List.map
               (fun l' ->
                 depth_first_search'
                   l'
                   label2
                   lattice
                   (label1 :: visited)
                   (label1 :: path))
               l)
        | None -> SAT
    in
    depth_first_search'
      (fst node1.data).data
      (fst node2.data).data
      lattice
      visited
      []

and compareSecurityLevels (node1 : sec_label') (node2 : sec_label') params env
    env2 =
  let compareParamList (list1 : sec_label_param' named_param' list)
      (list2 : sec_label_param' named_param' list) params env env2 =
    let listResult =
      List.map
        (fun param ->
          let find_param param_name list =
            match
              List.find_opt
                (fun el ->
                  let named, _ = el.data in
                  String.compare param_name named.data = 0)
                list
            with
            | Some s1 ->
              let _, value = s1.data in
              value.data
            | None -> Bot
          in
          match (find_param param list1, find_param param list2) with
          | Bot, _ | Parameterised _, Top | Top, Top -> SAT
          | Parameterised exp1, Parameterised exp2 -> (
            match (EvalExpr.evalExpr exp1 env, EvalExpr.evalExpr exp2 env2) with
            | Int n1, Int n2 ->
              if n1 == n2 then SAT
              else
                UNSAT
                  [ ( exp1.loc
                    , "Error in comparing exprs: " ^ unparse_expr exp1 ^ " = "
                      ^ unparse_expr exp2 )
                  ]
            | String n1, String n2 ->
              if String.compare n1 n2 == 0 then SAT
              else
                UNSAT
                  [ ( exp1.loc
                    , "Error in comparing exprs: " ^ unparse_expr exp1 ^ " = "
                      ^ unparse_expr exp2 )
                  ]
            | Bool n1, Bool n2 when n1 = n2 -> SAT
            | Error s, _ ->
              UNSAT
                [ ( exp1.loc
                  , "Error fst expr in comparing exprs: " ^ unparse_expr exp1
                    ^ " = " ^ unparse_expr exp2 )
                ; s
                ]
            | _, Error s ->
              UNSAT
                [ ( exp2.loc
                  , "Error snd expr in comparing exprs: " ^ unparse_expr exp1
                    ^ " = " ^ unparse_expr exp2 )
                ; s
                ]
            | Unknown, Unknown ->
              Unknown
                [ [ Positive (CnfSymEq (unparse_expr exp1, unparse_expr exp2)) ]
                ]
            | Unknown, Int s ->
              Unknown [ [ Positive (CnfEq (unparse_expr exp1, IntLit s)) ] ]
            | Unknown, Bool s ->
              Unknown [ [ Positive (CnfEq (unparse_expr exp1, BoolLit s)) ] ]
            | Unknown, String s ->
              Unknown [ [ Positive (CnfEq (unparse_expr exp1, StringLit s)) ] ]
            | Int s, Unknown ->
              Unknown [ [ Positive (CnfEq (unparse_expr exp2, IntLit s)) ] ]
            | Bool s, Unknown ->
              Unknown [ [ Positive (CnfEq (unparse_expr exp2, BoolLit s)) ] ]
            | String s, Unknown ->
              Unknown [ [ Positive (CnfEq (unparse_expr exp2, StringLit s)) ] ]
            | _ ->
              UNSAT
                [ ( exp1.loc
                  , "Error in comparing missmatch types exprs: "
                    ^ unparse_expr exp1 ^ " = " ^ unparse_expr exp2 )
                ])
          | _ ->
            UNSAT
              [ (node1.loc, "Error in comparing params of Security levels") ])
        params
    in
    let p = CnfExprCtxt.and_list listResult in
    p
  in
  (* let open Frontend in *)
  match (node1.data, node2.data) with
  | (s1, list_params1), (s2, list_params2)
    when String.compare s1.data s2.data = 0 -> (
    match TreeMap.find_opt s1.data !params with
    | Some param_list ->
      compareParamList list_params1 list_params2 param_list env env2
    | None -> UNSAT [ (node1.loc, "Error in security level comparison") ])
  | _ -> UNSAT [ (node1.loc, "Error in comparing security levels") ]

(* Get the node pc list without duplicates*)
(* Get the level from lists given a filter_function can be LuB(least upper
   bound) or GlB (greatest lower bound)*)
and get_levels_from_SC_List filter_function (pc_list : security_level)
    (pc2 : security_level) ctxt =
  let concatenated = pc_list @ pc2 in
  let noRepeatPc =
    List.fold_left
      (fun acc l ->
        if
          List.exists
            (fun l' ->
              match
                compareSecurityLevels l l' ctxt.sec_params ctxt.env ctxt.env
              with
              | SAT -> true
              | Unknown _ -> false
              | UNSAT _ -> false)
            acc
        then acc
        else l :: acc)
      []
      concatenated
  in
  filter_function noRepeatPc ctxt

(* public -> student student -> teacher student -> admin staff teacher ->
   academic manager admin staff -> academic manager academic manager -> secret

   glb (greatest lower bound) (teacher, admin) = student lub (least upper bound)
   (teacher, admin) = academic manager *)
(* Get the bottom levels of the list (least upper bound) Retorna todos os nos
   que têm caminho para outros*)
(* and filter_lower_levels (pc : sec_label' list) ctxt =
   let rec filter_levels (filtered : sec_label' list) = function
     | [] -> filtered
     | l :: ls ->
       let filtered' =
         List.filter
           (fun l' ->
             match
               depth_first_search
                 l
                 l'
                 !(ctxt.lattice)
                 []
                 ctxt.sec_params
                 ctxt.env
                 ctxt.env
             with
             | SAT -> false
             | _ -> true)
           filtered
       in
       filter_levels (l :: filtered') ls
   in
   filter_levels [] pc *)

(* Get the bottom levels of the list (least upper bound)   with tweaks *)
(*Retorna os nós que não têm caminhos*)
and filter_higher_levels (pc : sec_label' list) ctxt =
  let rec filter_levels (filtered : sec_label' list) = function
    | [] -> filtered
    | l :: ls ->
      let filtered' =
        List.filter
          (fun l' ->
            match
              depth_first_search
                l'
                l
                !(ctxt.lattice)
                []
                ctxt.sec_params
                ctxt.env
                ctxt.env
            with
            | SAT -> false
            | _ -> true)
          filtered
      in
      filter_levels (l :: filtered') ls
  in
  filter_levels [] pc

and concat_list list loc (ctxt : Ctxt.t) :
    (security_level, (loc * role_label) list) result =
  match
    List.fold_left
      (fun acc l ->
        match acc with
        | Error e -> Error ((loc, "Error in List") :: e)
        | Ok acc' -> (
          match l with
          | Ok l' -> Ok (acc' @ l')
          | Error e -> Error e))
      (Ok [])
      list
  with
  | Error e -> Error e
  | Ok result ->
    Ok (get_levels_from_SC_List filter_higher_levels result [] ctxt)
