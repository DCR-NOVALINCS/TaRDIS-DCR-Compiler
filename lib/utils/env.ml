type 'a t = (string * 'a) list list

let empty = [ [] ]

let rec bind (x : string) (v : 'a) (env : 'a t) =
  ((x, v) :: List.hd env) :: List.tl env

and bind_list (bindings : (string * 'a) list) (env : 'a t) : 'a t =
  List.fold_left (fun env (key, value) -> bind key value env) env bindings

let or_else v1 v2 =
  begin
    match v1 with
    | None -> v2 ()
    | Some v -> Some v
  end

let rec find_lvl_up (n : int) (x : string) (env : 'a t) : ('a * int) option =
  begin
    match env with
    | [] -> None
    | sc :: env ->
      if n == 0 then
        Option.bind (List.assoc_opt x sc) (fun v -> Option.some (v, n))
      else find_lvl_up (n - 1) x env
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

let find_flat (x : string) (env : 'a t) : 'a = fst @@ Option.get (find 1 x env)

(* let get x env = Option.get (find 1 x env) *)

let begin_scope (env : 'a t) : 'a t = [] :: env

let end_scope env =
  begin
    match env with
    | [] -> assert false
    | _ :: env -> env
  end

let to_assoc_list env = List.fold_left (fun acc lev -> lev @ acc) [] env

let decrease_nesting (x, (x', n)) = (x, (x', n - 1))

let to_string ~(fmt : 'a -> string) (env : 'a t) : string =
  let rec scope_to_str ?(acc = []) = function
    | [] -> acc
    | (k, v) :: xs ->
      scope_to_str ~acc:(Printf.sprintf "%s -> %s" k (fmt v) :: acc) xs
  in
  List.fold_left
    (fun (indent, acc) scope ->
      let acc =
        Printf.sprintf "%s> [%s]" indent (String.concat "; " @@ scope_to_str scope)
        :: acc
      in
      (indent ^ " ", acc))
    ("", [])
    (List.rev env)
  |> snd |> List.rev |> String.concat "\n"