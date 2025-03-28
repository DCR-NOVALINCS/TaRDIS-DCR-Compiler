module Choreo = Frontend.Syntax
open Choreo
open Sat
open Utils.Env
open Utils.Results
open Utils.Logs
open Frontend.Unparser

exception Typecheck_IFC_error of string

module TreeMap = Map.Make (String)

type ('a, 'b) leakError =
  | SAT
  | Unknown of 'a
  | UNSAT of 'b

let and_list (lst : (cnf_formula, (loc * element_uid) list) leakError list) :
    (cnf_formula, (loc * element_uid) list) leakError =
  let rec aux lst acc =
    match lst with
    | [] -> acc
    | x :: xs -> (
      match x with
      | UNSAT s -> UNSAT s
      | Unknown s -> begin
        match acc with
        | Unknown s' ->
          let p : cnf_formula = s @ s' in
          aux xs (Unknown p)
        | _ -> aux xs (Unknown s)
      end
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
      | UNSAT s ->
        (* print_endline "Unsat in or_list"; *)
        begin
          match acc with
          | UNSAT s' ->
            print_endline "Both unsat";
            aux xs (UNSAT (s @ s'))
          | _ -> aux xs acc
        end
      | Unknown s ->
        print_endline "Unknown in or_list";
        begin
          match acc with
          | Unknown s' ->
            let p : cnf_formula = s @ s' in
            aux xs (Unknown p)
          | UNSAT _ -> Unknown s
          | SAT -> aux xs acc
        end
      | SAT -> SAT)
  in
  (* print_endline "Or_list";
  print_int (List.length lst);
  print_endline ""; *)
  aux lst (UNSAT [ (Nowhere, "Error in or_list") ])

type level_t =
  { info : event_info'
  ; security_list : security_level
  ; io : data_expr
  ; kind : participants'
  }

(* =========================================================================
   ==================== DEBUG section (temporary: to remove) =============== *)

let debug_SCs id list =
  print_endline "====== [DEBUG start] SCs ===";
  print_endline @@ id ^ " : " ^ unparse_security_level' list;
  print_endline "====== [DEBUG end] SCs ==="

let unparse_level_t (level : level_t) =
  let id, label = level.info.data in
  id.data ^ " : " ^ label.data ^ " : "
  ^ unparse_security_level' level.security_list

let debug_env (env : level_t t) =
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

let _trigger : string = "@trigger"

let _CONSTANT_VALUE : string = "value"

let _BOT : string = "Bot"

let _TOP : string = "Top"

let _BOT_LEVEL : security_level = [ annotate (annotate _BOT, []) ]

let get_top_level (map : string list TreeMap.t) =
  try Some (fst (TreeMap.min_binding map)) with Not_found -> None

let get_label (lvl : sec_label') : string annotated =
  match lvl.data with
  | role, _ -> role

let get_label_from_SC (pc : value_dep_role_decl') : string annotated =
  match pc.data with
  | role, _ -> role

let rec stringfy_params ?(acc = "") expr =
  match expr.data with
  | True -> "true"
  | False -> "false"
  | IntLit n -> string_of_int n
  | StringLit s -> s
  | Parenthesized e -> "(" ^ stringfy_params ~acc e ^ ")"
  | EventRef id -> id.data
  | Trigger t -> t
  | PropDeref (e, prop) -> stringfy_params ~acc:(acc ^ "." ^ prop.data) e
  | _ -> acc

let security_labels : value_dep_role_decl' list ref = ref []

let global_label_SC : security_level TreeMap.t ref = ref TreeMap.empty

let mkNodeEvent (event : event) : level_t =
  { security_list = event.security_level.data
  ; io = event.data_expr.data
  ; info = event.info
  ; kind = event.participants
  }

let reset_references () =
  security_labels := [];
  global_label_SC := TreeMap.empty;
  Ok ()

let find_env env depth =
  let rec aux env depth =
    if depth = 0 then Ok env
    else if List.length env = 0 then Error "Error in find_env"
    else aux (end_scope env) (depth - 1)
  in
  match aux env depth with
  | Ok new_env -> Ok (env, new_env)
  | Error e -> Error e

module Local = struct
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
end

let rec evalExpr expr env depth : Local.evalExpr =
  match expr.data with
  | True -> Bool true
  | False -> Bool false
  | IntLit n -> Int n
  | StringLit s -> String s
  | Parenthesized exp -> evalExpr exp env depth
  | BinaryOp (exp1, exp2, op) ->
    let v1 = evalExpr exp1 env depth in
    let v2 = evalExpr exp2 env depth in
    begin
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
      | _ -> failwith "Invalid binary operation"
    end
  | UnaryOp (exp, op) -> begin
    match (op, evalExpr exp env depth) with
    | Minus, Int n -> Int (-n)
    | Negation, Bool b -> Bool (not b)
    | _ -> failwith "Invalid unary operation"
  end
  | PropDeref (e, prop) ->
    let rec evalProp e prop env n : ('a, 'b) Local.resultExpr =
      begin
        match e.data with
        | Trigger _ ->
          (* print_endline @@ "Depth in propDeref: " ^ string_of_int depth; *)
          begin
            match find_lvl_up (depth - 1) _trigger env with
            | None -> Local.Error (e.loc, "Trigger Event does not exist")
            | Some (node, _) -> (
              (* print_endline @@ unparse_level_t node; *)
              (* print_endline @@ "Depth in propDeref: " ^ string_of_int depth; *)
              match node.io with
              | Input _ -> Unknown
              | Computation expr -> Ok (expr, depth))
          end
        | EventRef e ->
          (* print_endline @@ e.data; *)
          (* debug_env env; *)
          begin
            match find 1 e.data env with
            | None -> Error (e.loc, "Event does not exist")
            | Some (node, depth) -> (
              match node.io with
              | Input _ -> Error (e.loc, "Not allowed, Input not implemented")
              | Computation expr -> Ok (expr, depth))
          end
        | PropDeref (e, prop2) ->
          (* prerr_endline "PropDeref in PropDeref";
              prerr_endline @@ "Prop1 in propDeref: " ^ prop.data; *)
          begin
            match evalProp e prop2 env n with
            | Ok (exp, depth) -> begin
              match exp.data with
              | Record rs -> begin
                match
                  List.find_opt
                    (fun x ->
                      let key, _ = x.data in
                      let p = String.compare key.data prop.data = 0 in
                      p)
                    rs
                with
                | None -> Error (e.loc, "Error in propDeref")
                | Some s ->
                  let _, expr = s.data in
                  Ok (expr, depth)
              end
              | _ -> Ok (exp, depth)
            end
            | Unknown -> Unknown
            | Error err ->
              Error (fst err, "Error in propDeref " ^ "\n" ^ snd err)
          end
        | _ -> Error (e.loc, "Invalid property dereference")
      end
    in
    (* print_endline @@ Unparser.unparse_expr e ^" :"^string_of_int depth; *)
    begin
      match evalProp e prop env depth with
      | Ok (expr, depth2) ->
        (* print_endline @@ Unparser.unparse_expr expr; *)
        (* print_endline @@ string_of_int depth2; debug_env env; *)
        evalExpr expr env depth2
      | Unknown -> Unknown
      | Error s -> Local.Error s
    end
  | _ -> failwith "Unhandled expression case: "

(* let translate_primitive_data_to_sec_level lattice (params:string list TreeMap.t): security_level=
    (* print_endline@@ "Translate primitive data to sec level";   *)
    let label_list = _BOT in
      let make_sec_lab label : sec_label'=   
        begin match TreeMap.find_opt label params with
        | None ->  print_endline @@ "Aqui" ;let p = annotate (annotate label, []) in p
        | Some list ->
            let list(* :sec_label_param' named_param' list*)= 
              List.map (fun name_param -> annotate ( annotate name_param,annotate Bot)) list in
            annotate (annotate label, list)
      end
      in List.map (fun label -> make_sec_lab label) label_list  *)

let rec check_static_information_security program =
  build_lattice
    program.roles
    program.security_lattice
    (ref TreeMap.empty)
    (ref TreeMap.empty)
  >>= fun (lattice, params) ->
  retrive_security_of_events
    (program.spawn_program.events, program.spawn_program.relations)
    (empty, lattice, params)
  >>= fun _ ->
  check_security_graph
    (program.spawn_program.events, program.spawn_program.relations)
    (empty, lattice, params, empty)
  >>= fun _ -> reset_references ()

and build_lattice (roles : value_dep_role_decl' list)
    (flw : flow_relation' list) (lattice : string list TreeMap.t ref)
    (sec_level_params : string list TreeMap.t ref) =
  let build_lattice_level (flw : flow_relation')
      (lattice : string list TreeMap.t ref) =
    let left, right = flw.data in
    match TreeMap.find_opt left.data !lattice with
    | Some l ->
      lattice := TreeMap.add left.data (right.data :: l) !lattice;
      Ok lattice
    | None ->
      Error
        [ (left.loc, "Error in lattice flow " ^ left.data ^ " -> " ^ right.data)
        ]
  in

  sec_level_params :=
    List.fold_left
      (fun acc level ->
        let label, params = level.data in
        let paramsLabel =
          List.map (fun (id, _) -> id.data) (deannotate_list params)
        in
        TreeMap.add label.data paramsLabel acc)
      !sec_level_params
      roles;

  lattice :=
    List.fold_left
      (fun acc label ->
        let label1, _ = label.data in
        TreeMap.add label1.data [] acc)
      !lattice
      roles;
  security_labels := roles;
  fold_left_error
    (fun levels_env f -> build_lattice_level f levels_env)
    lattice
    flw
  >>= fun lattice ->
  let all_parents = TreeMap.fold (fun key _ acc -> key :: acc) !lattice [] in
  let all_children =
    TreeMap.fold (fun _ values acc -> values @ acc) !lattice []
  in
  let is_leaf =
    List.filter (fun key -> not (List.mem key all_children)) all_parents
  in
  let is_root =
    List.filter (fun key -> not (List.mem key all_parents)) all_children
  in
  lattice := TreeMap.add _BOT is_leaf !lattice;
  lattice := TreeMap.add _TOP is_root !lattice;
  Ok (lattice, sec_level_params)

(** Function used to retrieve the security levels of all events in program. To
    be used in data of events. *)
and retrive_security_of_events (events, crs) (env, lattice, sec_parms) =
  let process_events (event : event') (env, lattice, sec_parms) =
    let all_levels_const (event_data : event) (env, lattice, sec_parms) =
      let security_level = event_data.security_level.data in
      List.for_all
        (fun sec_label ->
          let id, param = sec_label.data in
          print_endline @@ id.data;
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
    if all_levels_const event_data (env, lattice, sec_parms) then
      Ok (bind id.data (mkNodeEvent event_data) env, lattice, sec_parms)
    else
      Error
        [ ( event.loc
          , "Error in typechecking security level of event " ^ id.data ^ ":"
            ^ label.data )
        ]
    (* match !(event_data.security_level.ty) with 
        | None -> 
          
          
        | Some t -> if t.is_const then 
        else Error [(event.loc, "Security level parameter invalid in event " ^ id.data ^ ":" ^ label.data)] *)
  in
  let process_spawn_relation cr (env, level_map, sec_parms) =
    begin
      match cr.data with
      | ControlRelation _ -> Ok (env, level_map, sec_parms)
      | SpawnRelation (_, _, prog) ->
        retrive_security_of_events
          (prog.events, prog.relations)
          (begin_scope env, level_map, sec_parms)
        >>= fun (env2, level_map2, sec_params2) ->
        Ok (end_scope env2, level_map2, sec_params2)
    end
  in
  fold_left_error
    (fun tuple n -> process_events n tuple)
    (env, lattice, sec_parms)
    events
  >>= fun (env, level_map, security_lattice) ->
  fold_left_error
    (fun tuple cr -> process_spawn_relation cr tuple)
    (env, level_map, security_lattice)
    crs

and get_security_of_expr expr env lattice sec_params simbolic_env =
  begin
    match expr.data with
    | True -> Ok _BOT_LEVEL
    | False -> Ok _BOT_LEVEL
    | IntLit _ -> Ok _BOT_LEVEL
    | StringLit _ -> Ok _BOT_LEVEL
    | Parenthesized expr ->
      get_security_of_expr expr env lattice sec_params simbolic_env
    | BinaryOp (e1, e2, _) -> begin
      match get_security_of_expr e1 env lattice sec_params simbolic_env with
      | Error e -> Error ((e1.loc, "Error in exp node" ^ unparse_expr e1) :: e)
      | Ok pc1 -> (
        match get_security_of_expr e2 env lattice sec_params simbolic_env with
        | Error e -> Error ((e2.loc, "Error in exp node" ^ unparse_expr e2) :: e)
        | Ok pc2 ->
          Ok
            (get_levels_from_SC_List
               filter_higher_levels
               pc1
               pc2
               lattice
               sec_params
               env))
    end
    | UnaryOp (e, _) ->
      get_security_of_expr e env lattice sec_params simbolic_env
    | EventRef id -> begin
      match find_flat_opt id.data env with
      | None -> Error [ (id.loc, "Error in static check expr " ^ id.data) ]
      | Some node -> Ok node.security_list
    end
    | Trigger t -> begin
      match find_flat_opt _trigger env with
      | None -> Error [ (expr.loc, "Error in static check trigger " ^ t) ]
      | Some sec_node -> Ok sec_node.security_list
    end
    | PropDeref (expr, _) ->
      get_security_of_expr expr env lattice sec_params simbolic_env
    | List list ->
      let new_list =
        List.map
          (fun e -> get_security_of_expr e env lattice sec_params simbolic_env)
          list
      in
      concat_list new_list expr.loc lattice sec_params env
    | Record list ->
      let n_list =
        List.map
          (fun r ->
            get_security_of_expr
              (snd r.data)
              env
              lattice
              sec_params
              simbolic_env)
          list
      in
      concat_list n_list expr.loc lattice sec_params env
  end

(** Check security levels of graph 1. Verify events 2. Verify relations *)
and check_security_graph (events, crs) (env, lattice, sec_params, simbolic_env)
    =
  fold_left_error
    (fun tuple event -> check_security_event event tuple)
    (env, lattice, sec_params, simbolic_env)
    events
  >>= fun tuple1 ->
  fold_left_error (fun tuple cr -> check_security_relation cr tuple) tuple1 crs
  >>= fun tuple2 -> Ok tuple2

and check_security_relation cr (env, lattice, sec_params, simbolic_env) =
  begin
    match cr.data with
    | ControlRelation (e1, exp, e2, _) -> begin
      match get_security_of_expr exp env lattice sec_params simbolic_env with
      | Error e ->
        Error
          (( cr.loc
           , "Error in control relation checking event expression" ^ e1.data )
          :: e)
      | Ok security_level -> begin
        match (find_flat_opt e1.data env, find_flat_opt e2.data env) with
        | None, _ ->
          Error
            [ ( cr.loc
              , "Error in control relation finding event1 in " ^ e1.data
                ^ "flows" ^ e2.data )
            ]
        | _, None ->
          Error
            [ ( cr.loc
              , "Error in control relation finding event2 in " ^ e1.data
                ^ "flows" ^ e2.data )
            ]
        | Some node1, Some node2 ->
          let verify_relations_events () =
            (* debug_SCs e1.data node1.security_list;
          debug_SCs e2.data node2.security_list; *)
            begin
              match
                check_less_or_equal_security_level
                  node1.security_list
                  node2.security_list
                  sec_params
                  lattice
                  env
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
                print_endline @@ unparse_cnf_formula e;
                cr.ifc := Some true;
                Ok (env, lattice, sec_params, simbolic_env)
              | SAT -> Ok (env, lattice, sec_params, simbolic_env)
            end
          in
          begin
            match
              check_less_or_equal_security_level
                node1.security_list
                security_level
                sec_params
                lattice
                env
                false
            with
            | SAT -> verify_relations_events ()
            | UNSAT e ->
              Error
                (( cr.loc
                 , "Does not flow in control relation event to expression ("
                   ^ unparse_security_level' node1.security_list
                   ^ ") -> " ^ " ("
                   ^ unparse_security_level' security_level
                   ^ ")" )
                :: e)
            | Unknown e ->
              print_endline @@ unparse_cnf_formula e;
              exp.ifc := Some true;
              verify_relations_events ()
          end
      end
    end
    | SpawnRelation (event, exp, prog) ->
      (* Error [(cr.loc, "Error in spawn relation ")] *)
      begin
        match get_security_of_expr exp env lattice sec_params simbolic_env with
        | Error err ->
          Error ((exp.loc, "Error in event expression " ^ event.data) :: err)
        | Ok security_list -> begin
          match find_flat_opt event.data env with
          | None -> Error [ (cr.loc, "Error finding event: " ^ event.data) ]
          | Some node ->
            let spawn_creation () =
              let spawn_env = bind _trigger node @@ begin_scope env in
              begin
                match
                  check_security_graph
                    (prog.events, prog.relations)
                    (spawn_env, lattice, sec_params, simbolic_env)
                with
                | Ok (env2, lattice2, sec_params2, simb2) ->
                  Ok (end_scope env2, lattice2, sec_params2, simb2)
                | Error s -> Error ((cr.loc, "Error in spawn relation") :: s)
              end
            in
            begin
              match
                check_less_or_equal_security_level
                  node.security_list
                  security_list
                  sec_params
                  lattice
                  env
                  false
              with
              | UNSAT e ->
                Error
                  (( exp.loc
                   , "Error in event " ^ event.data ^ " expression "
                     ^ unparse_expr exp ^ " in spawn" )
                  :: e)
              | Unknown e ->
                print_endline @@ unparse_cnf_formula e;
                event.ifc := Some true;
                spawn_creation ()
              | SAT -> spawn_creation ()
            end
        end
      end
  end

(*1. Compare levels of the event with the trigger, if there is no trigger true
  2. Compare levels of the event with the data
  3. Check wellform *)
(* Verificar a correção das das expr? expr flow event_sec?*)
and check_security_event event (env, lattice, sec_params, simbolic_env) =
  (* debug_env env; *)
  let check_security_trigger (event : event') env lattice =
    begin
      match find_lvl_up 0 _trigger env with
      | None -> Ok ()
      | Some (data, depth) -> (
        if depth != 0 then Ok ()
        else
          match
            check_less_or_equal_security_level
              data.security_list
              event.data.security_level.data
              sec_params
              lattice
              env
              true
          with
          | UNSAT e ->
            Error ((event.loc, "Error in security with event and trigger") :: e)
          | SAT -> Ok ()
          | Unknown e ->
            print_endline @@ unparse_cnf_formula e;
            event.ifc := Some true;
            Ok ())
    end
  in

  let static_check_security_of_data_expr event env lattice sec_params
      simbolic_env =
    let rec check_security_of_type_expr type_expr lattice params =
      begin
        match type_expr.data with
        | UnitTy -> Ok _BOT_LEVEL
        | StringTy -> Ok _BOT_LEVEL
        | IntTy -> Ok _BOT_LEVEL
        | BoolTy -> Ok _BOT_LEVEL
        | EventRefTy (s, _) -> begin
          match TreeMap.find_opt s !global_label_SC with
          | None ->
            Error
              [ (type_expr.loc, "Error in static check Event type expr " ^ s) ]
          | Some node ->
            Ok
              (get_levels_from_SC_List
                 filter_higher_levels
                 node
                 []
                 lattice
                 sec_params
                 env)
        end
        | EventTy s -> begin
          match TreeMap.find_opt s !global_label_SC with
          | Some node ->
            Ok
              (get_levels_from_SC_List
                 filter_higher_levels
                 node
                 []
                 lattice
                 sec_params
                 env)
          | None ->
            Error
              [ (type_expr.loc, "Error in static check Event type expr " ^ s) ]
        end
        | RecordTy r ->
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
          begin
            match list_pc with
            | Error e -> Error e
            | Ok get_list ->
              Ok
                (get_levels_from_SC_List
                   filter_higher_levels
                   get_list
                   []
                   lattice
                   sec_params
                   env)
          end
        | ListTy _ ->
          Error [ (type_expr.loc, "Error in static check ListTy type expr ") ]
        | ListTyEmpty -> Ok _BOT_LEVEL
      end
    in
    begin
      match event.data_expr.data with
      | Input ty_expr -> begin
        match check_security_of_type_expr ty_expr lattice !sec_params with
        | Error e ->
          Error
            (( ty_expr.loc
             , "Error in expression of event " ^ (fst event.info.data).data
               ^ ":" ^ (snd event.info.data).data )
            :: e)
        | Ok security_lvl -> begin
          match
            check_less_or_equal_security_level
              event.security_level.data
              security_lvl
              sec_params
              lattice
              env
              false
          with
          | SAT -> Ok ()
          | UNSAT e ->
            Error
              (( ty_expr.loc
               , "Error static ifc in expression of event "
                 ^ (fst event.info.data).data ^ ":" ^ (snd event.info.data).data
               )
              :: e)
          | Unknown e ->
            print_endline @@ unparse_cnf_formula e;
            ty_expr.ifc := Some true;
            Ok ()
        end
      end
      | Computation expr -> begin
        match get_security_of_expr expr env lattice sec_params simbolic_env with
        | Error e ->
          Error
            (( expr.loc
             , "Error static ifc node exp " ^ (fst event.info.data).data ^ ":"
               ^ (snd event.info.data).data )
            :: e)
        | Ok security_level -> begin
          match
            check_less_or_equal_security_level
              event.security_level.data
              security_level
              sec_params
              lattice
              env
              false
          with
          | SAT -> Ok ()
          | UNSAT e ->
            Error
              (( expr.loc
               , "Error static ifc in node exp " ^ (fst event.info.data).data
                 ^ ":" ^ (snd event.info.data).data )
              :: e)
          | Unknown e ->
            print_endline @@ unparse_cnf_formula e;
            expr.ifc := Some true;
            Ok ()
        end
      end
    end
  in

  let check_wellformedness _ = Ok () in
  (* (security_level, (loc * element_uid) list) result list *)
  let static_checking_security_param (security_event : security_level) loc env
      lattice params =
    fold_left_error
      (fun (acc, env, lattice, params) (lvl : sec_label') ->
        let s1, list_params1 = lvl.data in
        let list_params_expr =
          List.map (fun (_, exp) -> exp.data) (deannotate_list list_params1)
        in
        let list_params =
          List.map
            (fun exp ->
              begin
                match exp with
                | Top -> Ok _BOT_LEVEL
                | Bot -> Ok _BOT_LEVEL
                | Parameterised exp1 ->
                  get_security_of_expr exp1 env lattice params simbolic_env
              end
              (* get_security_of_expr exp env lattice sec_params simbolic_env *))
            list_params_expr
        in
        match concat_list list_params loc lattice params env with
        | Ok l -> Ok (l @ acc, env, lattice, params)
        | Error e -> Error e
        (* Ok(acc,env,lattice,params) *))
      ([], env, lattice, params)
      security_event
    >>= fun (sec2, env2, lattice2, params2) ->
    Ok
      (get_levels_from_SC_List
         filter_higher_levels
         sec2
         []
         lattice2
         params2
         env2)
  in
  let id, label = event.data.info.data in
  match check_security_trigger event env lattice with
  | Error e ->
    Error
      (( event.data.info.loc
       , "Error checking ifc trigger in event " ^ id.data ^ ":" ^ label.data )
      :: e)
  | Ok () -> (
    match
      static_check_security_of_data_expr
        event.data
        env
        lattice
        sec_params
        simbolic_env
    with
    | Error e ->
      Error
        (( event.data.info.loc
         , "Error checking ifc levels in event " ^ id.data ^ ":" ^ label.data )
        :: e)
    | Ok () -> (
      (* bind data*)
      match check_wellformedness event with
      | Error e ->
        Error
          (( event.data.info.loc
           , "Error checking wellformedness in event " ^ id.data ^ ":"
             ^ label.data )
          :: e)
      | Ok _ -> (
        let new_env = bind id.data (mkNodeEvent event.data) env in
        match
          static_checking_security_param
            event.data.security_level.data
            Nowhere
            new_env
            lattice
            sec_params
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
              list
              sec_params
              lattice
              env
              false
          with
          | SAT -> Ok (new_env, lattice, sec_params, simbolic_env)
          | UNSAT e ->
            Error
              (( event.data.info.loc
               , "Error in static checking security param in event " ^ id.data
                 ^ ":" ^ label.data )
              :: e)
          | Unknown e ->
            (* prerr_endline @@ unparse e ; *)
            event.ifc := Some true;
            Ok (new_env, lattice, sec_params, simbolic_env)))))

and check_less_or_equal_security_level (event_security : security_level)
    (exp_security : security_level) sec_params lattice (env : level_t t)
    relation =
  (* print_endline "Check less or equal security level"; *)
  let debug_map_list (l : (cnf_formula, (loc * element_uid) list) leakError) =
    let open Printf in
    print_endline " ====== [DEBUG start] map_list ===";
    (* List.iter (fun m -> *)
    begin
      match l with
      | UNSAT _ -> print_endline "UNSAT"
      | SAT -> print_endline "SAT "
      | Unknown s -> unparse_cnf_formula s |> print_endline
    end;
    (* ) l; *)
    print_endline " ====== [DEBUG end] map_list ==="
  in
  let sat_list =
    List.map
      (fun node_2 ->
        (* print_endline @@ "Node2: " ^ (fst node_2.data).data; *)
        let aux_list =
          List.map
            (fun node_1 ->
              (* print_endline @@ "Node1: " ^ (fst node_1.data).data; *)
              if relation then
                depth_first_search node_1 node_2 !lattice [] sec_params env
              else
                let p =
                  depth_first_search node_2 node_1 !lattice [] sec_params env
                in
                debug_map_list p;
                p)
            event_security
        in
        or_list aux_list)
      exp_security
  in
  and_list sat_list

and depth_first_search (node1 : sec_label') (node2 : sec_label')
    (lattice : string list TreeMap.t) (visited : string list) params
    (env : level_t t) =
  if List.mem (fst node1.data).data visited then SAT
  else if (fst node1.data).data = (fst node2.data).data then
    compareSecurityLevels node1 node2 params env
  else
    let rec depth_first_search' (label1 : string) (label2 : string)
        (lattice : string list TreeMap.t) (visited : string list)
        (path : string list) =
      if List.mem label1 visited then SAT
      else if label1 = label2 then
        compareSecurityLevels (annotate (annotate label1, [])) node2 params env
      else begin
        match TreeMap.find_opt label1 lattice with
        | Some l ->
          or_list
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
      end
    in
    depth_first_search'
      (fst node1.data).data
      (fst node2.data).data
      lattice
      visited
      []

and compareSecurityLevels (node1 : sec_label') (node2 : sec_label') params env =
  let compareParamList (list1 : sec_label_param' named_param' list)
      (list2 : sec_label_param' named_param' list) params env =
    (*Fim do parameterised*)
    (*Return do paramList*)
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
          let create_cnf expr expr2 : cnf_formula =
            let sintringFy_expr1 = unparse_expr expr in
            let sintringFy_expr2 = unparse_expr expr2 in
            print_endline @@ "First expr: " ^ sintringFy_expr1;
            print_endline @@ "Second expr: " ^ sintringFy_expr2;
            [ [ Positive (CnfSymEq (sintringFy_expr1, sintringFy_expr2)) ] ]
          in
          match (find_param param list1, find_param param list2) with
          | Bot, _ | Parameterised _, Top | Top, Top -> SAT
          | Parameterised exp1, Parameterised exp2 -> begin
            match (evalExpr exp1 env 1, evalExpr exp2 env 1) with
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
            | Unknown, _ ->
              prerr_endline @@ "Unknown first expr in comparing exprs: "
              ^ unparse_expr exp1 ^ " = " ^ unparse_expr exp2;
              Unknown (create_cnf exp1 exp2)
            | _, Unknown ->
              prerr_endline @@ "Unknown snd expr in comparing exprs: "
              ^ unparse_expr exp1 ^ " = " ^ unparse_expr exp2;
              Unknown (create_cnf exp1 exp2)
            | _ ->
              UNSAT
                [ ( exp1.loc
                  , "Error in comparing exprs: " ^ unparse_expr exp1 ^ " = "
                    ^ unparse_expr exp2 )
                ]
          end
          | _ ->
            UNSAT
              [ (node1.loc, "Error in comparing params of Security levels") ])
        params
    in
    let p = and_list listResult in
    p
    (* match p with 
    | SAT -> print_endline @@ " SAT in compareList";SAT
    | UNSAT e -> print_endline @@ " UNSAT in compareList";UNSAT e
    | Unknown e -> print_endline @@ " Unknown in compareList";Unknown e *)
  in
  (* (element_uid, (loc * element_uid) list) leakError *)
  (* List de parametros {id:"1"}*)
  (* print_endline @@ "Comparing s1: " ^Unparser.unparse_sec_label' node1.data;
  print_endline @@ "Comparing s2: " ^Unparser.unparse_sec_label' node2.data; *)
  match (node1.data, node2.data) with
  | (s1, list_params1), (s2, list_params2)
    when String.compare s1.data s2.data = 0 -> (
    match TreeMap.find_opt s1.data !params with
    | Some param_list ->
      compareParamList list_params1 list_params2 param_list env
    | None -> UNSAT [ (node1.loc, "Error in security level comparison") ])
  | _ -> UNSAT [ (node1.loc, "Error in comparing security levels") ]

(* Get the node pc list without duplicates*)
(* Get the level from lists
  given a filter_function 
  can be LuB(least upper bound) or GlB (greatest lower bound)*)
and get_levels_from_SC_List filter_function (pc_list : security_level)
    (pc2 : security_level) lattice params (env : level_t t) =
  let concatenated = pc_list @ pc2 in
  let noRepeatPc =
    List.fold_left
      (fun acc l ->
        if
          List.exists
            (fun l' ->
              begin
                match compareSecurityLevels l l' params env with
                | SAT -> true
                | Unknown _ -> false
                | UNSAT _ -> false
              end)
            acc
        then acc
        else l :: acc)
      []
      concatenated
  in
  filter_function noRepeatPc lattice params env

(*
        public -> student  
        student -> teacher
        student -> admin staff 
        teacher -> academic manager
        admin staff -> academic manager
        academic manager -> secret

        glb (greatest lower bound) (teacher, admin) = student
        lub (least upper bound) (teacher, admin) = academic manager
      
      *)
(* Get the bottom levels of the list  (least upper bound)*)
(* Retorna todos os nos que têm caminho para outros*)
and filter_lower_levels (pc : sec_label' list) lattice params env =
  let rec filter_levels (filtered : sec_label' list) = function
    | [] -> filtered
    | l :: ls ->
      let filtered' =
        List.filter
          (fun l' ->
            match depth_first_search l l' !lattice [] params env with
            | SAT -> false
            | _ -> true)
          filtered
      in
      filter_levels (l :: filtered') ls
  in
  filter_levels [] pc

(* Get the bottom levels of the list (least upper bound)   with tweaks *)
(*Retorna os nós que não têm caminhos*)
and filter_higher_levels (pc : sec_label' list) lattice params env =
  let rec filter_levels (filtered : sec_label' list) = function
    | [] -> filtered
    | l :: ls ->
      let filtered' =
        List.filter
          (fun l' ->
            match depth_first_search l' l !lattice [] params env with
            | SAT -> false
            | _ -> true)
          filtered
      in
      filter_levels (l :: filtered') ls
  in
  filter_levels [] pc

and concat_list list loc lattice sec_params env :
    (security_level, (loc * role_label) list) result =
  begin
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
      Ok
        (get_levels_from_SC_List
           filter_higher_levels
           result
           []
           lattice
           sec_params
           env)
  end
