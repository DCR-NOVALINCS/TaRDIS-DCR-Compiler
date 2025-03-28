
(**
  Functions for debugging.    
*)
let ($.) f x = f x

(**
  Debugging function that returns a reference of a boolean list.    
*)
let debug_v = ref [false]

(**
  Function to start debugging.
*)
let start_debug () = debug_v := true :: !debug_v

(**
  Function to end debugging.    
*)
let end_debug () = debug_v := List.tl !debug_v

let debug f = start_debug (); let v = f() in end_debug (); v

(**
  Function to print a string if debugging is enabled.    
*)
let log_string s = if List.hd !debug_v then print_string s

(**
  Function to print an integer if debugging is enabled.
*)
let log_int s = if List.hd !debug_v then print_int s

(**
  Function to print a string with a newline if debugging is enabled.
*)
let log_endline s = if List.hd !debug_v then print_endline s

(**
  Function to print environment if debugging is enabled.
*)
let log_env env = log_endline $. String.concat "" (List.map (fun sc -> "["^(String.concat ";" (List.map (fun (x,x') -> (x^":"^x')) sc))^"]") env)

(**
  Function to print a list of 'a if debugging is enabled.
*)
let log_list f l = log_endline $. "["^(String.concat ";" (List.map f l))^"]"

(* let debug_env (env : Syntax.redaType Env.t_env) =
  let open Unparser in 
  let rec debug_aux env =
    match env with
    | [] -> print_endline "< end of level >\n"
    | (s, ty) :: xs ->
        print_endline @@ s ^ " : " ^ unparse_type ty true;
        debug_aux xs
  in
  print_endline "\n ====== [DEBUG start] Env ===\n";
  List.iter (fun scope -> debug_aux scope) env;
  print_endline " ====== [DEBUG end] Env ===\n"

let debug_global_label_nodes (nodes : (string * Syntax.redaType option ref) list ref) =
  print_endline "\n [debug] GLOBAL LABEL NODES:\n";
  let print_label (s1, s2) = 
    match !s2 with
    | None -> print_endline @@ s1 ^ " : <no type>"
    | Some ty -> print_endline @@ s1 ^ " : " ^ Unparser.unparse_type ty true
  in 
  List.iter print_label !nodes

let debug_global_nodes (nodes : Syntax.redaNode list ref) =
  let open Reda.Unparser in
  print_endline @@ "\n [debug] GLOBAL NODES:\n"
  ^ unparse_nodes " " !nodes  

let debug_template_defs (defs : Syntax.redaTemplateDef list) =
  let open Reda.Unparser in
  print_endline @@ "\n [debug] TEMPLATE DEFS:\n";
  List.iter (fun (def: Syntax.redaTemplateDef) -> 
      match def with
      | (id, params, _, returns) -> 
          print_endline @@ id ^ " ( " ^ 
            (String.concat ", " (List.map (fun node -> unparse_nodes " " [node]) params)) ^ ")->" ^
            (String.concat ", " returns) ^ "\n"
      | _ -> failwith "debug_template_defs: not a template def"
    ) defs

let debug_type (ty : Syntax.redaType) =
  let open Reda.Unparser in
  print_endline @@ "\n [debug] TYPE:\n" ^ unparse_type ty true

let debug_redaType (t : Syntax.redaType) =  
  print_endline @@ "\n [debug] REDA NODE TYPE:\n" ^ Unparser.unparse_type t true
  
let debug_exp (e : Syntax.redaExp) =
    print_endline @@ "\n [debug] REDA EXPRESSION:\n" ^ Unparser.unparse_expression e
  
let debug_redaPROP (p : Syntax.redaProp) =
    print_endline @@ "\n [debug] REDA PROP:\n" ^ p

  (* (redaType * redaType t_env, (loc * redaProp) list) optionError *)
let debug_reda r =
  let open Unparser in 
  print_endline @@ "Debugging reda";
  match r with
  | Ok (t, env) -> print_endline @@ "\n [debug] REDA NODE TYPE:\n" ^ unparse_type t true; debug_env env
  | Error(err ) -> (print_endline "Error debug reda"; 
        match err with
          | [] -> print_endline "Empty error";
          | _ -> List.iter (fun (l, s) -> print_endline @@ "Error: " ^ s) err)






let debug_global_env (global_env: (string * Syntax.redaType Env.t_env) list) =
  let open Reda.Unparser in
  print_endline @@ "\n [debug] GLOBAL ENV:\n";
  List.iter (fun (node, env) -> 
      print_endline @@ node ^ "\n";
      debug_env env
    ) global_env *)