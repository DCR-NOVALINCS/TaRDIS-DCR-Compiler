type 'a t = (string * 'a) list list

let empty = [ [] ]

let bind (x : string) (v : 'a) (env : 'a t) =
  ((x, v) :: List.hd env) :: List.tl env

let rec bind_list (bindings : (string * 'a) list) (env : 'a t) =
  List.fold_left
    (fun env binding -> (binding :: List.hd env) :: List.tl env)
    env
    bindings

let or_else v1 v2 =
  begin
    match v1 with
    | None -> v2 ()
    | Some v -> Some v
  end

let rec find_lvl_up (n:int) (x:string) (env:'a t) : ('a * int) option =
  begin match env with
    | [] -> None
    | sc :: env -> if n == 0 then(Option.bind (List.assoc_opt x sc) (fun v -> Option.some (v,n))) else find_lvl_up (n-1) x env
  end

let rec find (n : int) (x : string) (env : 'a t) : ('a * int) option =
  begin
    match env with
    | [] -> None
    | sc :: env ->
      or_else
        (Option.bind (List.assoc_opt x sc) (fun v -> Option.some (v, n)))
        (fun () -> find (n + 1) x env)
  end

let find_flat_opt (x : string) (env : 'a t) : 'a option =
  Option.bind (find 1 x env) (fun v -> Option.some (fst v))

  let find_flat (x : string) (env : 'a t) : 'a =
    fst @@ Option.get (find 1 x env)
  

(* let get x env = Option.get (find 1 x env) *)

let begin_scope env = [] :: env

let end_scope env =
  begin
    match env with
    | [] -> assert false
    | _ :: env -> env
  end

let to_assoc_list env =
  List.fold_left (fun acc lev -> lev @ acc ) [] env

let decrease_nesting (x, (x', n)) = (x, (x', n - 1))

let string_of_env v_fmt env =
  let rec string_of_scope sc =
    begin
      match sc with
      | [] -> ""
      | (x, v) :: sc -> x ^ " = " ^ v_fmt v ^ "; " ^ string_of_scope sc
    end
  in
  let rec string_of_env' n env =
    begin
      match env with
      | [] -> ""
      | sc :: env ->
        "Scope " ^ string_of_int n ^ ": { " ^ string_of_scope sc ^ " }" ^ "\n"
        ^ string_of_env' (n + 1) env
    end
  in
  string_of_env' 1 env

  (* TODO REVIEW *)

let bindings_at_level (level:int) (env:'a t): (string * 'a) list option = 
  if level < 0 then None else List.nth_opt env level 

let scope_bindings (env:'a t): (string * 'a) list = 
  List.hd env
  