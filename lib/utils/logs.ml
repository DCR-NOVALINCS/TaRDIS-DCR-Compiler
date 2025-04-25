
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
