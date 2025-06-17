module Choreo = Frontend.Syntax
open Choreo
open Sat
open Utils
open Utils.Results
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
  ; uuid : string option
  ; loc : loc
  ; env : node Env.t
  }

(* =========================================================================
   ==================== DEBUG section (temporary: to remove) =============== *)
let debug_map_list (l : (cnf_formula, (loc * element_uid) list) leakError) =
  match l with
  | UNSAT _ -> print_endline "UNSAT"
  | SAT -> print_endline "SAT "
  | Unknown s -> unparse_cnf_formula s |> print_endline

let debug_SCs id list =
  print_endline "====== [DEBUG start] SCs ===";
  print_endline @@ id ^ " : " ^ unparse_security_level' list;
  print_endline "====== [DEBUG end] SCs ==="

let unparse_level_t (level : node) =
  let id, label = level.info.data in
  id.data ^ " : " ^ label.data ^ " : "
  ^ unparse_security_level' level.security_list

let debug_env (env : node Env.t) =
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

let _BOT_LEVEL : security_level = [ annotate (Sec (annotate (annotate _BOT, []))) ]

let global_label_SC : security_level TreeMap.t ref = ref TreeMap.empty

module CnfExprCtxt : sig
  type mode =
    | Static
    | Dynamic
    | Hybrid

  type t =
    { symbolic_env : expr' Env.t
    ; contraints : cnf_formula TreeMap.t
    ; expr_map : expr' TreeMap.t
    ; dynamic_contraints : cnf_formula TreeMap.t
    ; mode : mode
    }

  val and_list :
       (cnf_formula, (loc * element_uid) list) leakError list
    -> (cnf_formula, (loc * element_uid) list) leakError

  val or_list :
       (cnf_formula, (loc * element_uid) list) leakError list
    -> (cnf_formula, (loc * element_uid) list) leakError

  val begin_scope : t -> t

  val end_scope : t -> t

  val empty : mode -> t

  val return_constainsts : t -> expr' TreeMap.t

  val update_cnf_formula :
    string -> cnf_formula -> t -> (t, loc * element_uid) result

  val cnf_expr : cnf_formula -> t -> expr'

  val update_expr'_env : string -> expr' -> t -> t

  val debug_contraints : t -> unit

  val debug_expr_env : expr' Env.t -> unit

  val debug_expr_TreeMap : expr list list TreeMap.t -> unit

  val debug_expr_TreeMap2 : expr' TreeMap.t -> unit
end = struct
  type mode =
    | Static
    | Dynamic
    | Hybrid

  type t =
    { symbolic_env : expr' Env.t
          (* string -> Expr ( stringfy da expr -> expr')*)
          (* TODO: Swap to expr' treemap?*)
    ; contraints : cnf_formula TreeMap.t (* string -> cnf ( uuid event -> cnf)*)
    ; expr_map : expr' TreeMap.t (* string -> expr' ( uuid event-> expr')*)
    ; dynamic_contraints :
        cnf_formula TreeMap.t (* string -> cnf ( uuid event -> cnf)*)
    ; mode : mode
    }

  let debug_expr_TreeMap2 expr_map =
       print_endline " ====== [DEBUG start] expr_map ===";
       TreeMap.iter
         (fun key value ->
           print_endline @@ key ^ " : " ^ unparse_expr value)
         expr_map;
     print_endline " ====== [DEBUG end] expr_map ==="
  let debug_expr_TreeMap expr_map =
    print_endline " ====== [DEBUG start] expr_map ===";
    let print_expr_list expr_list =
      List.map (fun expr -> unparse_expr (annotate expr)) expr_list
      |> String.concat ", " |> Printf.sprintf "[%s]"
    in
    TreeMap.iter
      (fun key (value : expr list list) ->
        print_string @@ key ^ " : ";
        let p = List.map (fun expr_list -> print_expr_list expr_list) value in
        p |> String.concat ", " |> Printf.sprintf "[%s]" |> print_endline)
      expr_map;
    print_endline " ====== [DEBUG end] expr_map ==="

  let debug_contraints ctxt =
    print_endline " ====== [DEBUG start] Constraints ===";
    print_endline @@ "Number of constraints: "
    ^ string_of_int (TreeMap.cardinal ctxt.contraints);
    TreeMap.iter
      (fun key value ->
        print_endline @@ key ^ " : " ^ unparse_cnf_formula value)
      ctxt.contraints;
    print_endline " ====== [DEBUG end] Constraints ==="

  let debug_expr_env (env : expr' Env.t) =
    let rec debug_aux env =
      match env with
      | [] -> print_endline "< end of level >\n"
      | (s, level) :: xs ->
        print_endline @@ s ^ " : " ^ unparse_expr level;
        debug_aux xs
    in
    print_endline "\n ====== [DEBUG start] Env ===\n";
    List.iter (fun scope -> debug_aux scope) env;
    print_endline " ====== [DEBUG end] Env ===\n"

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
          | UNSAT s' -> aux xs (UNSAT (s @ s'))
          | _ -> aux xs acc)
        | Unknown s -> (
          match acc with
          | Unknown s' ->
            let p : cnf_formula = cnf_or s s' in
            aux xs (Unknown p)
          | UNSAT _ -> Unknown s
          | SAT -> SAT)
        | SAT -> SAT)
    in
  
    aux
      lst
      (UNSAT [ (Nowhere, "[Error] While aggregating CNF formulas with OR") ])

  let empty mode : t =
    { symbolic_env = Env.empty
    ; contraints = TreeMap.empty
    ; expr_map = TreeMap.empty
    ; dynamic_contraints = TreeMap.empty
    ; mode
    }

  let begin_scope ctxt =
    { symbolic_env = Env.begin_scope ctxt.symbolic_env
    ; contraints = ctxt.contraints
    ; expr_map = ctxt.expr_map
    ; dynamic_contraints = ctxt.dynamic_contraints
    ; mode = ctxt.mode
    }

  let end_scope ctxt =
    { symbolic_env = Env.end_scope ctxt.symbolic_env
    ; contraints = ctxt.contraints
    ; expr_map = ctxt.expr_map
    ; dynamic_contraints = ctxt.dynamic_contraints
    ; mode = ctxt.mode
    }

  let cnf_expr (cnf : cnf_formula) ctxt : expr' =
    let const_to_expr c (env : expr' Env.t) =
      begin
        match c with
        | CnfSymEq (id1, id2) -> begin
          match (Env.find_flat_opt id1 env, Env.find_flat_opt id2 env) with
          | Some expr1, Some expr2 ->
            annotate
              ~loc:expr1.loc
              ~ty:(Some { t_expr = Choreo.BoolTy; is_const = false })
              (BinaryOp (expr1, expr2, Eq))
          | _, _ -> assert false
        end
        | CnfEq (id, value) -> begin
          match Env.find_flat_opt id env with
          | Some expr -> begin
            match value with
            | BoolLit b ->
              if b then
                annotate
                  ~loc:expr.loc
                  ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true })
                  (BinaryOp (expr, annotate True, Eq))
              else
                annotate
                  ~loc:expr.loc
                  ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true })
                  (BinaryOp (expr, annotate False, Eq))
            | IntLit i ->
              annotate
                ~loc:expr.loc
                ~ty:(Some { t_expr = Choreo.IntTy; is_const = true })
                (BinaryOp (expr, annotate (Choreo.IntLit i), Eq))
            | StringLit s ->
              annotate
                ~loc:expr.loc
                ~ty:(Some { t_expr = Choreo.StringTy; is_const = true })
                (BinaryOp (expr, annotate (Choreo.StringLit s), Eq))
          end
          | None -> assert false
        end
      end
    in
   let p =  List.filter (fun f -> f <> []) cnf in

     List.map (fun list ->
           let rec aux (literals : literal list) =
             begin
               match literals with
               | [] ->
                 annotate
                   ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true })
                   False
               | x :: xs ->
                 let expr_x =
                   begin
                     match x with
                     | Positive const -> const_to_expr const ctxt.symbolic_env
                     | Negative const ->
                       annotate
                         ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true })
                         (UnaryOp
                            (const_to_expr const ctxt.symbolic_env, Negation))
                   end
                 in
                 annotate
                   ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true })
                   (BinaryOp (expr_x, aux xs, Or))
             end
           in
           aux list) p
    |> List.fold_left
         (fun acc x ->
           annotate
             ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true })
             (BinaryOp (x, acc, And)))
         (annotate ~ty:(Some { t_expr = Choreo.BoolTy; is_const = true }) True)

  let update_cnf_formula (uuid : string) (cnf : cnf_formula) ctxt =
    let new_cnf =
      match TreeMap.find_opt uuid ctxt.contraints with
      | None -> cnf
      | Some cnf' -> cnf_and cnf cnf'
    in
    match cnf_sat_solve new_cnf with
    | None ->
      Error
        ( Nowhere
        , "[Error] Cnf sat solve: expression is unsat: "
          ^ unparse_cnf_formula new_cnf )
    | Some solver_cnf ->
      let aux =
        { symbolic_env = ctxt.symbolic_env
        ; contraints = TreeMap.add uuid solver_cnf ctxt.contraints
        ; expr_map = TreeMap.add uuid (cnf_expr solver_cnf ctxt) ctxt.expr_map
        ; dynamic_contraints =
            TreeMap.add uuid solver_cnf ctxt.dynamic_contraints
        ; mode = ctxt.mode
        }
      in
      Ok aux

  let return_constainsts ctxt =
    ctxt.expr_map
  

  let update_expr'_env (uuid : string) (expr : expr') ctxt =
    match Env.find_flat_opt uuid ctxt.symbolic_env with
    | Some _ -> ctxt
    | None -> { ctxt with symbolic_env = Env.bind uuid expr ctxt.symbolic_env }
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

  val create_and_bind_node : role_label -> event' -> t -> t

  val bind : role_label -> node -> t -> t

  val reset_references : t -> (expr' TreeMap.t, (loc * string) list) result

  val get_trigger : t -> string

  val add_symbol :
       string option
    -> loc
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
    let new_expr_map = CnfExprCtxt.return_constainsts ctxt.symbolic in
    begin
      match ctxt.symbolic.mode with
      | Hybrid -> Ok new_expr_map
      | Static ->
        if new_expr_map = TreeMap.empty then Ok new_expr_map
        else Error [ (Nowhere, "[Error] Static verification not possible") ]
      | Dynamic -> Error [ (Nowhere, " Dynamic verification not implemented") ]
    end

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

  let add_symbol uuid loc cnf error ctxt =
    begin
      match uuid with
      | Some uuid -> begin
        match CnfExprCtxt.update_cnf_formula uuid cnf ctxt.symbolic with
        | Error e ->
          Error
            (( loc
             , "[Error] While adding dynamic flag in CnfExprCtxt: "
               ^ unparse_cnf_formula cnf )
            :: [ e ])
        | Ok symbolic -> Ok { ctxt with symbolic }
      end
      | None -> Error [ (loc, error) ]
    end

  let create_and_bind_node id node ctxt : t =
    let mkNodeEvent (event : event') env : node =
      { security_list = event.data.security_level.data
      ; io = event.data.data_expr.data
      ; info = event.data.info
      ; kind = event.data.participants
      ; uuid = !(event.uid)
      ; env
      ; loc = event.loc
      }
    in
    { ctxt with env = Env.bind id (mkNodeEvent node ctxt.env) ctxt.env }

  let bind id node ctxt : t = { ctxt with env = Env.bind id node ctxt.env }

  let find_env (depth : int) (ctxt : t) =
    let rec aux (env : node Env.t) (depth : int) =
      if depth = 0 then Ok env
      else if List.length env = 0 then
        Error
          [ ( Nowhere
            , "[Error] While trying to find an environment with depth "
              ^ string_of_int depth )
          ]
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
      | _ -> failwith ("Invalid binary operation: " ^ unparse_expr expr))
    | UnaryOp (exp, op) -> (
      match (op, evalExpr exp env) with
      | Minus, Int n -> Int (-n)
      | Negation, Bool b -> Bool (not b)
      | _ -> failwith ("Invalid unary operation" ^ unparse_expr expr))
    | PropDeref (e, prop) -> (
      let rec evalProp e prop env : ('a, 'b) resultExpr =
        match e.data with
        | Trigger t -> (
          match Env.find_flat_opt t env with
          | None -> Error (e.loc, "[Error] Trigger event does not exist")
          | Some node -> (
            match node.io with
            | Input _ -> Unknown
            
            | Computation expr -> Ok (expr, node.env)))
        | EventRef e -> (
          match Env.find_flat_opt e.data env with
          | None -> Error (e.loc, "[Error] Event does not exist")
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
              | None ->
                Error
                  ( e.loc
                  , "[Error] In propDeref: Record entry not found: " ^ prop.data
                  )
              | Some s ->
                let _, expr = s.data in
                Ok (expr, env2))
            | _ -> Ok (expr, env2))
          | Unknown -> Unknown
          | Error err ->
            Error
              ( fst err
              , "   [Error] Evaluating dereference value: " ^ prop2.data ^ "\n"
                ^ snd err ))
        | _ -> Error (e.loc, "[Error] Invalid property dereference")
      in
      match evalProp e prop env with
      | Ok (expr, env2) -> evalExpr expr env2
      | Unknown -> Unknown
      | Error s -> Error s)
    | _ -> failwith "   Unhandled expression case "
end

let rec check_static_information_security program =
  let ctxt : Ctxt.t =
    { env = Env.empty
    ; lattice = ref TreeMap.empty
    ; sec_params = ref TreeMap.empty
    ; symbolic = CnfExprCtxt.empty Hybrid
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
  >>= fun final_ctxt -> Ctxt.reset_references final_ctxt

and build_lattice (roles : value_dep_role_decl' list)
    (flw : flow_relation' list) (ctxt : Ctxt.t) =
  let build_lattice_level (ctxt : Ctxt.t) (flw : flow_relation') =
    let left, right = flw.data in
    match TreeMap.find_opt left.data !(ctxt.lattice) with
    | Some l ->
      ctxt.lattice := TreeMap.add left.data (right.data :: l) !(ctxt.lattice);
      Ok ctxt
    | None ->
      Error
        [ ( left.loc
          , "[Error] Building the lattice in edge: " ^ left.data ^ " -> "
            ^ right.data )
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
          begin match sec_label.data with
          | Sec sec -> let _, param = sec.data in
            begin match param with
            | [] -> true
            | xs ->
              List.for_all
                (fun x ->
                  match !(x.ty) with
                  | None -> true
                  | Some t -> t.is_const)
                xs
              end
          | SecExpr _ -> true
          end)
        security_level
    in
    let event_data = event.data in
    let id, label = event_data.info.data in
    global_label_SC :=
      TreeMap.add label.data event_data.security_level.data !global_label_SC;

    if all_levels_const event_data then
      Ok (Ctxt.create_and_bind_node id.data event ctxt)
    else
      Error
        [ ( event.loc
          , "[Error] Checking if all security parameters are constants in: "
            ^ id.data ^ ":" ^ label.data )
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
    | Error e ->
      Error
        ((e1.loc, "[Error] Getting security level of expr: " ^ unparse_expr e1)
        :: e)
    | Ok pc1 -> (
      match get_security_of_expr ctxt e2 with
      | Error e ->
        Error
          ((e2.loc, "[Error] Getting security level of expr: " ^ unparse_expr e2)
          :: e)
      | Ok pc2 -> Ok (get_levels_from_SC_List filter_higher_levels pc1 pc2 ctxt)
      ))
  | UnaryOp (e, _) -> get_security_of_expr ctxt e
  | EventRef id -> (
    match Env.find_flat_opt id.data ctxt.env with
    | None ->
      Error [ (id.loc, "[Error] Getting security level of event: " ^ id.data) ]
    | Some node -> Ok node.security_list)
  | Trigger t -> (
    match Env.find_flat_opt t ctxt.env with
    | None ->
      Error [ (expr.loc, "[Error] Getting security level of trigger: " ^ t) ]
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

(** Check security levels of graph 
  1. Verify events 
  2. Verify relations *)
and check_security_graph (ctxt : Ctxt.t) (events, crs) =
  fold_left_error check_security_event ctxt events >>= fun ctxt1 ->
  fold_left_error check_security_relation ctxt1 crs >>= fun ctxt2 -> Ok ctxt2

and check_security_relation (ctxt : Ctxt.t) cr =
  match cr.data with
  | ControlRelation (e1, exp, e2, _) -> (
    match get_security_of_expr ctxt exp with
    | Error e ->
      Error
        (( cr.loc
         , "[Error]In control relation checking guard expression: "
           ^ unparse_expr exp )
        :: e)
    | Ok security_level -> (
      match
        (Env.find_flat_opt e1.data ctxt.env, Env.find_flat_opt e2.data ctxt.env)
      with
      | None, _ ->
        Error
          [ ( cr.loc
            , "[Error]In control relation finding first event in " ^ e1.data
              ^ "flows" ^ e2.data )
          ]
      | _, None ->
        Error
          [ ( cr.loc
            , "[Error]In control relation finding second event in " ^ e1.data
              ^ "flows" ^ e2.data )
          ]
      | Some node1, Some node2 -> (
        let verify_relations_events (cond : cnf_formula) symbolic =
          let ctxt = { ctxt with symbolic } in
          match
            check_less_or_equal_security_level
              node1.security_list
              node1.env
              node2.security_list
              node2.env
              ctxt.sec_params
              ctxt.lattice
              ctxt.symbolic
              true
          with
          | _, UNSAT e ->
            Error
              (( cr.loc
               , "[Error]Information leak in control relation " ^ e1.data
                 ^ "("
                 ^ unparse_security_level' node1.security_list
                 ^ ") -> " ^ e2.data ^ " ("
                 ^ unparse_security_level' node2.security_list
                 ^ ")" )
              :: e)
          | symbolic, Unknown e ->
            let ctxt = { ctxt with symbolic } in
            Ctxt.add_symbol
              !(cr.uid)
              cr.loc
              (cnf_and cond e)
              "[Error]In control relation: Invalid relation uuid while adding \
               dynamic flag in Unknown"
              ctxt
          | symbolic, SAT ->
            let ctxt = { ctxt with symbolic } in
            Ctxt.add_symbol
              !(cr.uid)
              cr.loc
              cond
              "[Error]In control relation: Invalid relation uuid while adding \
               dynamic flag in SAT"
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
            ctxt.symbolic
            false
        with
        | new_ctxt, SAT -> verify_relations_events [] new_ctxt
        | _, UNSAT e ->
          Error
            (( cr.loc
             , "[Error]Information leak in control relation: event to \
                expression ("
               ^ unparse_security_level' node1.security_list
               ^ ") -> " ^ " ("
               ^ unparse_security_level' security_level
               ^ ")" )
            :: e)
        | new_ctxt, Unknown e -> verify_relations_events e new_ctxt)))
  | SpawnRelation (event, trigger_label, exp, prog) -> (
    match get_security_of_expr ctxt exp with
    | Error err ->
      Error
        ((exp.loc, "[Error] Checking spawn guard expression " ^ event.data)
        :: err)
    | Ok security_list -> (
      match Env.find_flat_opt event.data ctxt.env with
      | None ->
        Error [ (cr.loc, "[Error] finding the trigger event: " ^ event.data) ]
      | Some node -> (
        let spawn_creation ctxt =
          let new_ctxt =
            Ctxt.begin_scope trigger_label ctxt |> Ctxt.bind trigger_label node
          in
          match check_security_graph new_ctxt (prog.events, prog.relations) with
          | Ok ctxt2 -> Ok (Ctxt.end_scope ctxt2)
          | Error s ->
            Error ((cr.loc, "[Error] Checking security in spawn relation") :: s)
        in
        match
          check_less_or_equal_security_level
            node.security_list
            node.env
            security_list
            ctxt.env
            ctxt.sec_params
            ctxt.lattice
            ctxt.symbolic
            false
        with
        | _, UNSAT e ->
          Error
            (( exp.loc
             , "[Error]In event " ^ event.data ^ " expression "
               ^ unparse_expr exp ^ " in spawn" )
            :: e)
        | symbolic, Unknown e -> begin
          match
            Ctxt.add_symbol
              !(cr.uid)
              cr.loc
              e
              "[Error]In control relation: Invalid relation uuid in Spawn"
              { ctxt with symbolic }
          with
          | Error e ->
            Error
              (( exp.loc
               , "[Error]In event " ^ event.data ^ " expression "
                 ^ unparse_expr exp ^ " in spawn" )
              :: e)
          | Ok ctxt2 -> spawn_creation ctxt2
        end
        | symbolic, SAT -> spawn_creation { ctxt with symbolic })))

(*1. Compare levels of the event with the trigger, if there is no trigger true
  2. Compare levels of the event with the data
  3. Check wellform *)
and check_security_event (ctxt : Ctxt.t) event =
  let check_security_trigger (event : event') (ctxt : Ctxt.t) =
      
    if ctxt.trigger_stack = [] then Ok ctxt
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
          ctxt.symbolic
          true
      with
      | _, UNSAT e ->
        Error
          (( event.loc
           , "[Error] Infomation leak in event trigger "
             ^ unparse_event_info event.data.info.data
             ^ " with trigger event "
             ^ unparse_event_info trigger_node.info.data )
          :: e)
      | symbolic, SAT -> Ok { ctxt with symbolic }
      | symbolic, Unknown e ->
        Ctxt.add_symbol
          !(event.uid)
          event.loc
          e
          "[Error] Event: Invalid event trigger uuid in Unknown "
          { ctxt with symbolic }
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
            [ (type_expr.loc, "[Error] Static check Event type expr " ^ s) ]
        | Some node ->
          Ok (get_levels_from_SC_List filter_higher_levels node [] ctxt))
      | EventTy s -> (
        match TreeMap.find_opt s !global_label_SC with
        | Some node ->
          Ok (get_levels_from_SC_List filter_higher_levels node [] ctxt)
        | None ->
          Error
            [ (type_expr.loc, "[Error] Static check Event type expr " ^ s) ])
      | RecordTy r -> (
        let list_pc =
          List.fold_left
            (fun acc l ->
              match acc with
              | Error e -> Error ((type_expr.loc, "[Error] RecordTy") :: e)
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
        Error [ (type_expr.loc, "[Error] Static check ListTy type expr ") ]
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
           , "[Error] Expression of event " ^ (fst event.info.data).data ^ ":"
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
            ctxt.symbolic
            false
        with
        | symbolic, SAT -> Ok ({ ctxt with symbolic }, [])
        | _, UNSAT e ->
          Error
            (( ty_expr.loc
             , "[Error] Static ifc in expression of event "
               ^ (fst event.info.data).data ^ ":" ^ (snd event.info.data).data
             )
            :: e)
        | symbolic, Unknown e -> Ok ({ ctxt with symbolic }, e)))
    | Computation expr -> (
      match get_security_of_expr ctxt expr with
      | Error e ->
        Error
          (( expr.loc
           , "[Error] Static ifc node exp " ^ (fst event.info.data).data ^ ":"
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
            ctxt.symbolic
            false
        with
        | symbolic, SAT -> Ok ({ ctxt with symbolic }, [])
        | _, UNSAT e ->
          Error
            (( expr.loc
             , "[Error] static ifc in node exp " ^ (fst event.info.data).data
               ^ ":" ^ (snd event.info.data).data )
            :: e)
        | symbolic, Unknown e ->
          Ok ({ ctxt with symbolic }, e)))
  in

  let check_wellformedness _ = Ok [] in
  let static_checking_security_param (security_event : security_level) loc ctxt
      =
    fold_left_error
      (fun (acc, ctxt) (lvl : sec_label') ->
        begin match lvl.data with
        | SecExpr exp1 -> 
          begin match concat_list
            [ get_security_of_expr ctxt exp1 ]
            loc ctxt with
          | Error e -> Error e
          | Ok l -> Ok (l @ acc, ctxt)
          end
        | Sec lvl ->
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
        | Error e -> Error e
      end)
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
       , "[Error] Checking ifc trigger in event " ^ id.data ^ ":" ^ label.data )
      :: e)
  | Ok ctxt1 -> (
    match static_check_security_of_data_expr event.data ctxt1 with
    | Error e ->
      Error
        (( event.data.info.loc
         , "[Error] Checking ifc levels in event " ^ id.data ^ ":" ^ label.data )
        :: e)
    | Ok (ctxt, cnf_list2) -> (
      match check_wellformedness event with
      | Error e ->
        Error
          (( event.data.info.loc
           , "[Error] Checking wellformedness in event " ^ id.data ^ ":"
             ^ label.data )
          :: e)
      | Ok cnf_list3 -> (
        let new_ctxt = Ctxt.create_and_bind_node id.data event ctxt in
        match
          static_checking_security_param
            event.data.security_level.data
            Nowhere
            new_ctxt
        with
        | Error e ->
          Error
            (( event.data.info.loc
             , "[Error] Checking security parameters in event " ^ id.data ^ ":"
               ^ label.data )
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
              ctxt.symbolic
              false
          with
          | symbolic, SAT ->
            let new_cond = cnf_and cnf_list2 cnf_list3 in

            begin
              match
                Ctxt.add_symbol
                  !(event.uid)
                  event.data.info.loc
                  new_cond
                  "[Error] Event: Invalid event uuid in SAT"
                  { new_ctxt with symbolic }
              with
              | Error e ->
                Error
                  (( event.data.info.loc
                   , "[Error] Static checking security param in event "
                     ^ id.data ^ ":" ^ label.data )
                  :: e)
              | Ok new_ctxt -> Ok new_ctxt
            end
          | _, UNSAT e ->
            Error
              (( event.data.info.loc
               , "[Error] Static checking security param in event " ^ id.data
                 ^ ":" ^ label.data )
              :: e)
          | symbolic, Unknown e ->
            let new_cond = cnf_and e (cnf_and cnf_list2 cnf_list3) in
            begin
              match
                Ctxt.add_symbol
                  !(event.uid)
                  event.data.info.loc
                  new_cond
                  "[Error] Event: Invalid event uuid in Unknown"
                  { new_ctxt with symbolic }
              with
              | Error e ->
                Error
                  (( event.data.info.loc
                   , "[Error] Checking security paramarameters in event "
                     ^ id.data ^ ":" ^ label.data )
                  :: e)
              | Ok new_ctxt -> Ok new_ctxt
            end))))

and check_less_or_equal_security_level (event_security : security_level)
    (env : node Env.t) (exp_security : security_level) (env2 : node Env.t)
    sec_params lattice symbolic_env relation =
  let first_list = ref event_security in
  let snd_list = ref exp_security in
  let (new_ctxt, sat_list) :
      CnfExprCtxt.t * (cnf_formula, (loc * role_label) list) leakError list =
    List.fold_left
      (fun (ctx1, list) l ->
        let resCtxt, resList =
          List.fold_left
            (fun (ctxt2, list2) node_1 ->
              begin match l.data , node_1.data with
              | Sec exp1, Sec exp2 -> 
                let ctxt3, list3 = 
                if relation then 
                  depth_first_search
                exp2
                exp1
                    !lattice
                    []
                    sec_params
                    env
                    env2
                    ctxt2
                  else
                    depth_first_search
                    exp1
                    exp2
                    !lattice
                    []
                    sec_params
                    env2
                    env
                    ctxt2
                  in 
           
                     (ctxt3, list3 :: list2)
                | SecExpr exp1 , SecExpr exp2 -> 
                  let unp1 = unparse_expr exp1 in
                  let unp2 = unparse_expr exp2 in 
                  if (String.compare unp1 unp2) = 0 then  
                    (ctx1, SAT::list2)
                  else 
                    (ctx1, UNSAT[(exp1.loc, "[Error] Comparing both security levels "^unp1 ^" <> "^unp2)]::list2)
                | Sec lvl , SecExpr _ -> 
                  if relation then 
                  (ctx1, UNSAT[(lvl.loc, "[Error] Comparing both security levels, lvl with exp ")]::list2)
                else 
                  (ctx1, SAT::list2)
              | SecExpr exp1 , Sec _ ->
                if relation then 
                  (ctx1, SAT::list2)
                else 
                  (ctx1, UNSAT[(exp1.loc, "[Error] Comparing both security levels, exp with lvl")]::list2)
              end)
            (ctx1, []) !first_list
        in
        let resolve_or:(cnf_formula, (loc * role_label) list) leakError list = [CnfExprCtxt.or_list (resList@list)] in
        (resCtxt,resolve_or))
      (symbolic_env, [])
      !snd_list
  in
  (new_ctxt, CnfExprCtxt.and_list sat_list)

and depth_first_search (node1 : sec_label_param' parameterisable_role') (node2 : sec_label_param' parameterisable_role')
    (lattice : string list TreeMap.t) (visited : string list) params
    (env : node Env.t) env2 symbolic =
  if List.mem (fst node1.data).data visited then (symbolic, SAT)
  else if (fst node1.data).data = (fst node2.data).data then
    compareSecurityLevels node1 node2 params env env2 symbolic
  else
    let rec depth_first_search' (label1 : string) (label2 : string)
        (lattice : string list TreeMap.t) (visited : string list)
        (path : string list) symbolic2 =
      if List.mem label1 visited then (symbolic2, SAT)
      else if label1 = label2 then
        compareSecurityLevels
          (annotate (annotate label1, []))
          node2
          params
          env
          env2
          symbolic2
      else
        match TreeMap.find_opt label1 lattice with
        | Some l ->
          let acc, list =
            List.fold_left
              (fun (acc, list) l' ->
                let acc', l' =
                  depth_first_search'
                    l'
                    label2
                    lattice
                    (label1 :: visited)
                    (label1 :: path)
                    acc
                in
                (acc', l' :: list))
              (symbolic2, [])
              l
          in
          (acc, CnfExprCtxt.or_list list)
        | None -> (symbolic2, SAT)
    in
    depth_first_search'
      (fst node1.data).data
      (fst node2.data).data
      lattice
      visited
      []
      symbolic

and compareSecurityLevels (node1 : sec_label_param' parameterisable_role') (node2 : sec_label_param' parameterisable_role') params env
    env2 symbolic =
  let compareParamList (list1 : sec_label_param' named_param' list)
      (list2 : sec_label_param' named_param' list) params env env2
      (symbolic : CnfExprCtxt.t) =
    let listResult :
        CnfExprCtxt.t * (cnf_formula, (loc * role_label) list) leakError list =
      List.fold_left
        (fun (ctxt, list) param ->
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
          | Bot, _ | Parameterised _, Top | Top, Top -> (ctxt, SAT :: list)
          
          | Parameterised exp1, Parameterised exp2 -> (
            let symb1 = unparse_expr exp1 in
            let symb2 = unparse_expr exp2 in
            let new_ctxt =
              CnfExprCtxt.update_expr'_env
                symb2
                exp2
                (CnfExprCtxt.update_expr'_env symb1 exp1 ctxt)
            in
            match (EvalExpr.evalExpr exp1 env, EvalExpr.evalExpr exp2 env2) with
            | Int n1, Int n2 ->
              if n1 == n2 then (ctxt, SAT :: list)
              else
                ( ctxt
                , UNSAT
                    [ ( exp1.loc
                      , "[Error] Expected two identical integers, actual \
                         values: " ^ unparse_expr exp1 ^ " = "
                        ^ unparse_expr exp2 )
                    ]
                  :: list )
            | String n1, String n2 ->
              if String.compare n1 n2 == 0 then (ctxt, SAT :: list)
              else
                ( ctxt
                , UNSAT
                    [ ( exp1.loc
                      , "[Error] Expected two identical strings, got: "
                        ^ unparse_expr exp1 ^ " = " ^ unparse_expr exp2 )
                    ]
                  :: list )
            | Bool n1, Bool n2 when n1 = n2 -> (ctxt, SAT :: list)
            | Error s, _ ->
              ( ctxt
              , UNSAT
                  [ ( exp1.loc
                    , "[Error] Expected two identical strings, got: "
                      ^ unparse_expr exp1 ^ " = " ^ unparse_expr exp2 )
                  ; s
                  ]
                :: list )
            | _, Error s2 ->
              ( ctxt
              , UNSAT
                  [ ( exp2.loc
                    , "[Error] Processing the second expression: "
                      ^ unparse_expr exp1 ^ " = " ^ unparse_expr exp2 )
                  ; s2
                  ]
                :: list )
            | Unknown, Unknown ->
              ( new_ctxt
              , Unknown [ [ Positive (CnfSymEq (symb1, symb2)) ] ] :: list )
            | Unknown, Int s ->
              ( new_ctxt
              , Unknown [ [ Positive (CnfEq (symb1, IntLit s)) ] ] :: list )
            | Unknown, Bool s ->
              ( new_ctxt
              , Unknown [ [ Positive (CnfEq (symb1, BoolLit s)) ] ] :: list )
            | Unknown, String s ->
              ( new_ctxt
              , Unknown [ [ Positive (CnfEq (symb1, StringLit s)) ] ] :: list )
            | Int s, Unknown ->
              ( new_ctxt
              , Unknown [ [ Positive (CnfEq (symb2, IntLit s)) ] ] :: list )
            | Bool s, Unknown ->
              ( new_ctxt
              , Unknown [ [ Positive (CnfEq (symb2, BoolLit s)) ] ] :: list )
            | String s, Unknown ->
              ( new_ctxt
              , Unknown [ [ Positive (CnfEq (symb2, StringLit s)) ] ] :: list )
            | _ ->
              ( ctxt
              , UNSAT
                  [ ( exp1.loc
                    , "[Error] Comparing missmatch types exprs: "
                      ^ unparse_expr exp1 ^ " = " ^ unparse_expr exp2 )
                  ]
                :: list ))
          | _ ->
            ( ctxt
            , UNSAT
                [ ( node1.loc
                  , "[Error] Comparing params values of Security levels" )
                ]
              :: list ))
        (symbolic, [])
        params
    in
    let p = CnfExprCtxt.and_list (snd listResult) in
    (fst listResult, p)
  in
  match (node1.data, node2.data) with
  | (s1, list_params1), (s2, list_params2)
    when String.compare s1.data s2.data = 0 -> (
    match TreeMap.find_opt s1.data !params with
    | Some param_list ->
      compareParamList list_params1 list_params2 param_list env env2 symbolic
    | None ->
      ( symbolic
      , UNSAT
          [ ( node1.loc
            , "[Error] When verifying security level in loc "
              ^ string_of_loc node1.loc ^ " and/or " ^ string_of_loc node2.loc
            )
          ] ))
  | _ ->
    ( symbolic
    , UNSAT
        [ (node1.loc, "[Error] When verifying security level, missmatch levels") ]
    )

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
              begin match l.data, l'.data with
              | Sec l, Sec l' ->
                begin match
                  compareSecurityLevels
                    l
                    l'
                    ctxt.sec_params
                    ctxt.env
                    ctxt.env
                    ctxt.symbolic
                with
                | _, SAT -> true
                | _, Unknown _ -> false
                | _, UNSAT _ -> false
              end
              | SecExpr expr, SecExpr expr2 -> String.compare (unparse_expr expr)
                (unparse_expr expr2) = 0
              | _ , _ -> false
              end)
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
(* Get the bottom levels of the list (least upper bound)   with tweaks *)
(*Retorna os nós que não têm caminhos*)
and filter_higher_levels (pc : sec_label' list) ctxt =
  let rec filter_levels (filtered : sec_label' list) = function
    | [] -> filtered
    | l :: ls ->
      let filtered':sec_label' list =
        List.filter
          (fun l' ->
            begin match l.data, l'.data with
            | Sec secl, Sec secl' -> 
            begin match
              depth_first_search
                secl'
                secl
                !(ctxt.lattice)
                []
                ctxt.sec_params
                ctxt.env
                ctxt.env
                ctxt.symbolic
            with
            | _, SAT -> false
            | _ -> true 
            end
            | SecExpr expr, SecExpr expr2 -> String.compare (unparse_expr expr)
              (unparse_expr expr2) = 0
            | Sec _ , SecExpr _ -> true
            | SecExpr _, Sec _ -> false
            end
          
          )
          filtered
      in
      filter_levels (l :: filtered') ls
  in
  filter_levels [] pc

(**)
and concat_list list loc (ctxt : Ctxt.t) :
    (security_level, (loc * role_label) list) result =
  match
    List.fold_left
      (fun acc l ->
        match acc with
        | Error e ->
          Error ((loc, "[Error] While concatenating security levels ") :: e)
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