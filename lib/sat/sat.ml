module Choreo = Frontend.Syntax
open Choreo

module DisjointSet : sig
  type t = identifier list * int Array.t

  val init : identifier list -> t

  val union : identifier -> identifier -> t -> t

  val find : identifier -> t -> identifier

  val flatten : t -> t
end = struct
  type t = identifier list * int Array.t

  let init (symbols : identifier list) : t =
    (symbols, Array.init (List.length symbols) Fun.id)

  let rec find_ idx partition =
    let partition = Array.copy partition in
    if partition.(idx) = idx then idx
    else
      let rep = find_ partition.(idx) partition in
      (* path compression *)
      partition.(idx) <- rep;
      rep

  and union_ idx1 idx2 partition =
    let partition = Array.copy partition in
    partition.(find_ idx2 partition) <- partition.(find_ idx1 partition)
  (* partition *)

  and find (sym : identifier) ((symbols, partition) : t) =
    let idx = Option.get (List.find_index (String.equal sym) symbols) in
    let rep = partition.(find_ idx partition) in
    List.nth symbols rep

  and union (sym1 : identifier) (sym2 : identifier) ((symbols, partition) : t) =
    let partition = Array.copy partition in
    let idx1 = Option.get (List.find_index (String.equal sym1) symbols)
    and idx2 = Option.get (List.find_index (String.equal sym2) symbols) in
    let rep1 = partition.(find_ idx1 partition)
    and rep2 = partition.(find_ idx2 partition) in
    if rep1 < rep2 then partition.(rep2) <- partition.(rep1)
    else partition.(rep1) <- partition.(rep2);
    (symbols, partition)

  and flatten ((symbols, partition) : t) =
    (symbols, Array.map (fun idx -> partition.(find_ idx partition)) partition)
end

(* concrete param value in a userset role expression *)
type param_value =
  | BoolLit of bool
  | IntLit of int
  | StringLit of string

(* restriction over a param_val *)
(* and param_val_constraint =
  (* same as '*' *)
  | Unconstrained
  (* determined constant value *)
  | Determined of param_value
  (* Excludes some constant values *)
  | Excludes of param_value list
  (* Binded to a symbolic constant which is known only at runtime *)
  | Binded of identifier *)
and cnf_bool_constraint =
  | CnfSymEq of identifier * identifier
  | CnfEq of identifier * param_value

and literal =
  | Positive of cnf_bool_constraint
  | Negative of cnf_bool_constraint

(* we can consider a restricted type of formulas, given the way we'll be
   building them *)
and formula =
  | Literal of literal
  | Disjunction of formula * formula
  | Conjunction of formula * formula

(* TODO renaming -> normal_form: then use the same representation
   for both CNF and DNF and distinguish according to name / context*)
and cnf_clause = literal list

and cnf_formula = cnf_clause list

(* let counter = ref 0 *)

(** [list_combine f [a1; ...; an] [b1; ...; bm]] returns the list
    [[f a1 b1; f a1 b2; ...; f an bm]], resulting from applying function [f] to
    each element in the cartesian product of [[a1; ...; an]] and
    [[b1; ...; bm]]. *)
let list_combine : 'a 'b 'c. ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list =
 fun combinator l1 l2 ->
  List.concat (List.map (fun l1 -> List.map (fun l2 -> combinator l1 l2) l2) l1)

let rec unparse_param_val = function
  | BoolLit bool_val -> string_of_bool bool_val
  | IntLit int_val -> string_of_int int_val
  | StringLit str_val -> str_val

(* and unparse_param_val_constraint = function
  | Unconstrained -> "*"
  | Determined value -> unparse_param_val value
  | Excludes exclude_list ->
    List.map (fun x -> Printf.sprintf "!=%s" (unparse_param_val x)) exclude_list
    |> String.concat ", "
  | Binded symbol -> symbol *)

and unparse_cnf_constraint = function
  | CnfSymEq (id1, id2) -> Printf.sprintf "(%s = %s)" id1 id2
  | CnfEq (id, value) ->
    Printf.sprintf "(%s = %s)" id @@ unparse_param_val value

and unparse_variable = function
  | Positive constr -> unparse_cnf_constraint constr
  | Negative constr -> Printf.sprintf "~%s" @@ unparse_cnf_constraint constr

and unparse_cnf_clause clause =
  List.map unparse_variable clause
  |> String.concat ", " |> Printf.sprintf "[%s]"

and unparse_cnf_formula (cnf : cnf_formula) =
  List.map unparse_cnf_clause cnf |> String.concat ", " |> Printf.sprintf "[%s]"

and param_val_compare param1 param2 =
  match (param1, param2) with
  | BoolLit bool1, BoolLit bool2 -> Bool.compare bool1 bool2
  | IntLit int1, IntLit int2 -> Int.compare int1 int2
  | StringLit str1, StringLit str2 -> String.compare str1 str2
  | BoolLit _, IntLit _ -> -1
  | BoolLit _, StringLit _ -> -1
  | IntLit _, StringLit _ -> -1
  | _ -> 1

(* and cnf_constraint_compare constr1 constr2 =
  match (constr1, constr2) with
  | CnfSymEq (id1, id2), CnfSymEq (id3, id4) ->
    if id1 = id3 then String.compare id2 id4 else String.compare id1 id3
  | CnfEq (id1, v1), CnfEq (id2, v2) ->
    if id1 = id2 then param_val_compare v1 v2 else String.compare id1 id2
  | CnfSymEq _, CnfEq _ -> -1
  | CnfEq _, CnfSymEq _ -> 1 *)

and cnf_constraint_compare constr1 constr2 =
  match (constr1, constr2) with
  | CnfEq (id1, v1), CnfEq (id2, v2) ->
    if id1 = id2 then param_val_compare v1 v2 else String.compare id1 id2
  | CnfSymEq (id1, id2), CnfSymEq (id3, id4) ->
    if id1 = id3 then String.compare id2 id4 else String.compare id1 id3
  | CnfEq _, _ -> -1
  | _ -> 1

and literal_compare lit1 lit2 =
  match (lit1, lit2) with
  | Positive constr1, Positive constr2 | Negative constr1, Negative constr2 ->
    cnf_constraint_compare constr1 constr2
  | Positive c1, Negative c2 ->
    let cmp = cnf_constraint_compare c1 c2 in
    if cmp = 0 then -1 else cmp
  | Negative c1, Positive c2 ->
    let cmp = cnf_constraint_compare c1 c2 in
    if cmp = 0 then 1 else cmp

and cnf_clause_compare (c1 : cnf_clause) (c2 : cnf_clause) =
  let length_compare = List.compare_lengths c1 c2 in
  if length_compare <> 0 then length_compare
  else
    let sorted_c1 = List.sort literal_compare c1
    and sorted_c2 = List.sort literal_compare c2 in
    List.compare literal_compare sorted_c1 sorted_c2

and extract_lit_symbols = function
  | Positive (CnfSymEq (s1, s2)) | Negative (CnfSymEq (s1, s2)) -> [ s1; s2 ]
  | Positive (CnfEq (s, _)) | Negative (CnfEq (s, _)) -> [ s ]

and extract_cnf_symbols (cnf : cnf_formula) =
  List.concat (List.concat (List.map (List.map extract_lit_symbols) cnf))
  |> List.sort_uniq String.compare

and negate = function
  | Positive v -> Negative v
  | Negative v -> Positive v

and cnf_simplify (cnf : cnf_formula) : cnf_formula =
  let rec tautology_elimination cnf_formula =
    let rec is_tautology = function
      | [] | _ :: [] -> false
      | x1 :: x2 :: xs ->
        if x1 = negate x2 then true else is_tautology (x2 :: xs)
    in
    List.filter (fun x -> not (is_tautology x)) cnf_formula
  in
  List.sort_uniq cnf_clause_compare cnf
  |> List.map (List.sort_uniq literal_compare)
  |> tautology_elimination

and dnf_to_cnf (dnf : cnf_formula) : cnf_formula =
  let rec find_common_opt cnf = function
    | [] -> None
    | x :: xs ->
      if List.for_all (List.exists (fun e -> e = x)) cnf then Some x
      else find_common_opt cnf xs
  and factorize ((acc, dnf) : cnf_formula * cnf_formula) =
    match List.sort_uniq List.compare_lengths dnf with
    | [] -> (acc, [])
    | [] :: xs -> factorize (acc, xs)
    | (_ :: _ as hd) :: _ -> begin
      match find_common_opt dnf hd with
      | None -> (acc, dnf)
      | Some lit ->
        let dnf = List.map (List.filter (fun x -> x <> lit)) dnf in
        factorize ([ lit ] :: acc, dnf)
    end
  and convert = function
    | ([] | [ _ ]) as res -> res
    | x1 :: x2 :: xs ->
      let res =
        List.fold_left
          (fun acc x -> list_combine (fun clause lit -> lit :: clause) acc x)
          (list_combine (fun x y -> [ x; y ]) x1 x2)
          xs
      in
      res
  in
  let cnf, dnf = factorize ([], dnf) in
  let res =
    cnf @ convert dnf
    |> (fun x -> List.sort_uniq cnf_clause_compare x)
    |> (fun x -> cnf_simplify x)
    |> List.sort_uniq cnf_clause_compare
  in
  res

module SolutionSet = struct
  type sym = identifier

  and solution =
    { syms : sym list
    ; connected : DisjointSet.t
    ; values : (sym * param_value option) list
    ; constraints : literal list
    }

  and t =
    | Unsat
    | Sat of solution

  let simplify (sol : literal list) =
    let rec propagate_sym_value (sym, value) ?(acc = []) = function
      | [] -> acc
      | lit :: xs -> begin
        match lit with
        | Positive (CnfSymEq (s1, s2)) ->
          if s1 = sym then
            let acc = Positive (CnfEq (s2, value)) :: acc in
            propagate_sym_value (sym, value) ~acc xs
          else if s2 = sym then
            let acc = Positive (CnfEq (s1, value)) :: acc in
            propagate_sym_value (sym, value) ~acc xs
          else
            let acc = lit :: acc in
            propagate_sym_value (sym, value) ~acc xs
        | Negative (CnfSymEq (s1, s2)) ->
          if s1 = sym then
            let acc = Negative (CnfEq (s2, value)) :: acc in
            propagate_sym_value (sym, value) ~acc xs
          else if s2 = sym then
            let acc = Negative (CnfEq (s1, value)) :: acc in
            propagate_sym_value (sym, value) ~acc xs
          else
            let acc = lit :: acc in
            propagate_sym_value (sym, value) ~acc xs
        | _ -> propagate_sym_value (sym, value) ~acc:(lit :: acc) xs
      end
    in
    let rec propagate_positive_lits (propagated_lits, other_lits) = function
      | [] -> propagated_lits @ other_lits
      | x :: xs -> begin
        match x with
        | Positive (CnfEq (sym, value)) as lit ->
          let propagate_res =
            propagate_sym_value (sym, value) (other_lits @ xs)
          in
          propagate_positive_lits (lit :: propagated_lits, []) propagate_res
        | _ as lit ->
          propagate_positive_lits (propagated_lits, lit :: other_lits) xs
      end
    in
    propagate_positive_lits ([], []) sol

  let unparse_value_bindings (bs : (sym * param_value option) list) =
    let unparse_value_binding (b : sym * param_value option) =
      let sym, param_val_opt = b in
      match param_val_opt with
      | Some expr -> Printf.sprintf "(%s, %s)" sym (unparse_param_val expr)
      | None -> Printf.sprintf "(%s,None)" sym
    in
    List.map (fun x -> unparse_value_binding x) bs
    |> String.concat ", "
    |> Printf.sprintf "values: (%s)"

  let to_string (t : t) =
    match t with
    | Unsat -> "Unsat"
    | Sat sol ->
      let value_bindings = unparse_value_bindings sol.values in
      let constraints =
        List.map unparse_cnf_clause [ sol.constraints ]
        |> String.concat ", " |> Printf.sprintf "[%s]"
      in
      Printf.sprintf
        "\n------------\n%s\n%s\n----------\n"
        value_bindings
        constraints

  let sat_check (sol : solution) : t =
    let cc = sol.connected in
    let checks_out = function
      | Positive (CnfSymEq (s1, s2)) ->
        DisjointSet.find s1 cc = DisjointSet.find s2 cc
      | Negative (CnfSymEq (s1, s2)) ->
        DisjointSet.find s1 cc <> DisjointSet.find s2 cc
      | Positive (CnfEq (s, expr)) ->
        let rep = DisjointSet.find s sol.connected in
        let val_opt = List.assoc rep sol.values in
        val_opt = Some expr
      | Negative (CnfEq (s, expr)) ->
        let rep = DisjointSet.find s sol.connected in
        let val_opt = List.assoc rep sol.values in
        val_opt <> Some expr
    in
    let constraints = simplify sol.constraints in
    (* print_endline @@ Printf.sprintf "@sat_check: constraints= %s" (unparse_cnf_clause constraints); *)
    if List.for_all checks_out constraints then Sat sol else Unsat

  let init (symbols : identifier list) : t =
    let solution =
      { syms = symbols
      ; connected = DisjointSet.init symbols
      ; values = List.map (fun s -> (s, None)) symbols
      ; constraints = []
      }
    in
    Sat solution

  let rec unify_value (r : sym) (v : param_value)
      (values : (sym * param_value option) list) =
    (* lookup previous sym-val association *)
    let ((_, param_opt) as b_curr) =
      List.find (fun (rep, _) -> rep = r) values
    in
    begin
      match param_opt with
      | None ->
        (* bind value - sat checked by the caller *)
        let b = (r, Some v) in
        (* TODO refactor in terms of List.remove_assoc *)
        (* let _ = List.remove_assoc sym values  in *)
        let values = b :: List.filter (fun x -> x <> b_curr) values in
        Some values
      | Some v_prev -> if v_prev = v then Some values else None
    end

  (** Takes representatives [r1] and [r2] and unifies the *)
  and unify_syms r1 r2 connected values =
    (* DEBUGS *)
    let unify r b1 b2 lit_opt values =
      let b = (DisjointSet.find r connected, lit_opt) in
      let values = b :: List.filter (fun x -> x <> b1 && x <> b2) values in
      Some values
    (* bindings associated to each representative *)
    and b1 = List.find (fun (rep, _) -> rep = r1) values
    and b2 = List.find (fun (rep, _) -> rep = r2) values in
    begin
      match (b1, b2) with
      | (_, Some val1), (_, Some val2) ->
        if val1 <> val2 then None else unify r1 b1 b2 (Some val1) values
      | (_, None), (_, Some lit) | (_, Some lit), (_, None) ->
        unify r1 b1 b2 (Some lit) values
      | _ -> unify r1 b1 b2 None values
    end

  (* simplification (for now): literals with unknown symbols are ignored
     (may have the downside of silently ignoring errors...) *)
  (* failed literals yield Unsat *)
  and add_literal (lit : literal) (sol : t) =
    let sol =
      match sol with
      | Sat sol -> begin
        let sol = { sol with constraints = lit :: sol.constraints |> simplify }
        and syms = extract_lit_symbols lit in
        if
          not
            (List.fold_left (fun acc s -> acc && List.mem s sol.syms) true syms)
        then Sat sol
        else begin
          match lit with
          | Positive (CnfSymEq (s1, s2)) ->
            let r1 = DisjointSet.find s1 sol.connected
            and r2 = DisjointSet.find s2 sol.connected in
            if r1 = r2 then Sat sol
            else
              let connected =
                DisjointSet.union s1 s2 sol.connected |> DisjointSet.flatten
              in
              begin
                match unify_syms r1 r2 connected sol.values with
                | Some values -> sat_check { sol with connected; values }
                | None -> Unsat
              end
          | Negative (CnfSymEq (s1, s2)) ->
            let r1 = DisjointSet.find s1 sol.connected
            and r2 = DisjointSet.find s2 sol.connected in
            (* if r1 = r2 then Unsat else Sat sol *)
            if r1 = r2 then Unsat else sat_check sol
          | Positive (CnfEq (s, expr)) ->
            let r = DisjointSet.find s sol.connected in
            begin
              match unify_value r expr sol.values with
              | Some values -> sat_check { sol with values }
              | None -> Unsat
            end
          | Negative (CnfEq (s, expr)) ->
            let r = DisjointSet.find s sol.connected in
            (* TODO [revisit] *)
            (* if List.assoc r sol.values <> Some expr then Sat sol else Unsat *)
            if List.assoc r sol.values <> Some expr then Sat sol
            else sat_check sol
        end
      end
      | Unsat -> Unsat
    in
    sol
end

let print_solution_set sol =
  match sol with
  | Some sat ->
    List.iter
      (fun sol ->
        print_endline (Printf.sprintf "\nSolution: %s" (unparse_cnf_clause sol)))
      sat
  | None -> print_endline "\n\nUnsat!\n"

let rec make_sym_eq_constraint id1 id2 =
  let left, right =
    if String.compare id1 id2 <= 0 then (id1, id2) else (id2, id1)
  in
  CnfSymEq (left, right)

and is_tautology (clause : cnf_clause) =
  List.exists
    (fun (x, y) -> x = negate y)
    (list_combine (fun x y -> (x, y)) clause clause)

(** DPLL-based procedure (tentative: add conflict-driven clause learning *)
and cnf_sat_solve (cnf : cnf_formula) : cnf_formula option =
  let bind_sol some = function
    | SolutionSet.Unsat -> None
    | SolutionSet.Sat _ as sol -> some sol
  in
  let rec propagate_lit lit = function
    | [] -> []
    | c :: cs ->
      if List.mem lit c then propagate_lit lit cs
      else List.filter (fun x -> x <> negate lit) c :: propagate_lit lit cs
  and unit_propagate (assigned : SolutionSet.t) (cnf : cnf_formula) =
    (* obs: non-tail-rec to keep ascending order by clause-lenght *)
    let unit_propagate (assigned : SolutionSet.t) = function
      | [] :: _ -> None
      | [ x ] :: xs ->
        bind_sol
          (fun sol -> unit_propagate sol (propagate_lit x xs))
          (SolutionSet.add_literal x assigned)
      | _ as tail -> Some (assigned, tail)
    in
    (* remove duplicates and redundants *)
    let cnf = cnf_simplify cnf in
    let cnf = List.sort List.compare_lengths cnf in
    unit_propagate assigned cnf
  and dpll_all_sat ((all_sat, assigned) : SolutionSet.t list * SolutionSet.t) =
    function
    | [] -> Some (assigned :: all_sat)
    | [] :: _ -> None
    | (_ :: []) :: _ as cs -> begin
      match unit_propagate assigned cs with
      | None -> None
      | Some (assigned, cnf) -> dpll_all_sat (all_sat, assigned) cnf
    end
    | (lit :: (_ :: _ as tail)) :: cs -> (
      let pos1 =
        bind_sol
          (fun sol -> dpll_all_sat (all_sat, sol) (propagate_lit lit cs))
          (SolutionSet.add_literal lit assigned)
      and neg1 =
        bind_sol
          (fun sol ->
            dpll_all_sat
              (all_sat, sol)
              (propagate_lit (negate lit) (tail :: cs)))
          (SolutionSet.add_literal (negate lit) assigned)
      in
      match (pos1, neg1) with
      | Some sat1, Some sat2 -> Some (sat1 @ sat2 @ all_sat)
      | Some sat, None | None, Some sat -> Some (sat @ all_sat)
      | _ -> if List.is_empty all_sat then None else Some all_sat
      (* Some all_sat *))
  in
  let cnf = cnf_simplify cnf in
  let sol = extract_cnf_symbols cnf |> SolutionSet.init in
  let res = dpll_all_sat ([], sol) cnf in
  Option.bind res (fun lst ->
      Some
        (List.filter_map
           (function
             | SolutionSet.Unsat -> None
             | SolutionSet.Sat sol -> Some sol.constraints)
           lst
        |> (fun lst -> lst)
        (* |> cnf_simplify *)
        |> dnf_to_cnf
        |> List.sort cnf_clause_compare))

(* variant of cnf_sat_solve - return every solution found
   TODO decide on merging with flag or keeping separate with fatorizations *)
and cnf_all_sat_solve (cnf : cnf_formula) : cnf_formula list =
  let bind_sol some = function
    | SolutionSet.Unsat -> None
    | SolutionSet.Sat _ as sol -> some sol
  in
  let rec propagate_lit lit = function
    | [] -> []
    | c :: cs ->
      if List.mem lit c then propagate_lit lit cs
      else List.filter (fun x -> x <> negate lit) c :: propagate_lit lit cs
  and unit_propagate (assigned : SolutionSet.t) (cnf : cnf_formula) =
    (* reminder: non-tail-rec to keep ascending order by clause-lenght *)
    let unit_propagate (assigned : SolutionSet.t) = function
      | [] :: _ -> None
      | [ x ] :: xs ->
        bind_sol
          (fun sol -> unit_propagate sol (propagate_lit x xs))
          (SolutionSet.add_literal x assigned)
      | _ as tail -> Some (assigned, tail)
    in
    (* remove duplicates and redundants *)
    let cnf = cnf_simplify cnf in
    let cnf = List.sort List.compare_lengths cnf in
    unit_propagate assigned cnf
  and dpll_all_sat ((all_sat, assigned) : SolutionSet.t list * SolutionSet.t) =
    function
    | [] -> Some (assigned :: all_sat)
    | [] :: _ -> None
    | (_ :: []) :: _ as cs -> begin
      match unit_propagate assigned cs with
      | None -> None
      | Some (assigned, cnf) -> dpll_all_sat (all_sat, assigned) cnf
    end
    | (lit :: (_ :: _ as tail)) :: cs -> (
      let pos1 =
        bind_sol
          (fun sol -> dpll_all_sat (all_sat, sol) (propagate_lit lit cs))
          (SolutionSet.add_literal lit assigned)
      in
      let neg1 =
        bind_sol
          (fun sol ->
            dpll_all_sat
              (all_sat, sol)
              (propagate_lit (negate lit) (tail :: cs)))
          (SolutionSet.add_literal (negate lit) assigned)
      in
      match (pos1, neg1) with
      | Some sat1, Some sat2 -> Some (sat1 @ sat2 @ all_sat)
      | Some sat, None | None, Some sat -> Some (sat @ all_sat)
      | _ -> Some all_sat)
  in

  (* TODO chain calls *)
  (* TODO maybe use sort_unique here or ensure any CNF already entails no duplicates *)
  (* let cnf =
       List.sort cnf_clause_compare cnf
       |> cnf_simplify
       |> List.sort cnf_clause_compare
     in *)
  let cnf = List.sort_uniq cnf_clause_compare cnf in
  let cnf = cnf_simplify cnf in
  let cnf = List.sort cnf_clause_compare cnf in
  let sol = extract_cnf_symbols cnf |> SolutionSet.init in

  (* print_string "---\n\n\n\n\n  @cnf_sat_solve [on entry]:\n   ";
  print_endline (unparse_cnf_formula cnf);
  print_endline "=========================================\n\n\n\n"; *)
  Option.fold
    (dpll_all_sat ([], sol) cnf)
    ~none:[]
    ~some:(fun lst ->
      (* List.iter (fun sol -> print_endline @@ SolutionSet.to_string sol) lst; *)
      List.filter_map
        (function
          | SolutionSet.Unsat -> None
          | SolutionSet.Sat sol -> Some sol.constraints)
        lst
      (* |> List.map SolutionSet.simplify *)
      |> List.fold_left
           (fun acc lst -> List.map (fun lit -> [ lit ]) lst :: acc)
           []
      (* |> List.map (List.sort_uniq cnf_clause_compare) *)
      |> List.map cnf_simplify
      (* |> List.map cnf_factorize *))

and cnf_entails (cnf_formula : cnf_formula) (cnf_clause : cnf_clause) =
  (* print_endline @@ Printf.sprintf "@cnf_entails - kb: %s" (unparse_cnf_formula cnf_formula);
  print_endline @@ Printf.sprintf "@cnf_entails - clause: %s" (unparse_cnf_formula [cnf_clause]);
  let negated = cnf_neg [cnf_clause] in
  print_endline @@ Printf.sprintf "@cnf_entails - negated clause: %s" (unparse_cnf_formula negated);
  let res = List.is_empty @@ cnf_all_sat_solve @@ cnf_and cnf_formula @@ cnf_neg [cnf_clause]
in 
print_endline @@ Printf.sprintf "entails is %b" res;
res *)
  List.is_empty @@ cnf_all_sat_solve @@ cnf_and cnf_formula
  @@ cnf_neg [ cnf_clause ]

and is_unit_clause clause = List.length clause = 1

and is_failed_clause clause = List.length clause = 0

(** [cnf_and cnf1 cnf2] returns a CNF formula equivalent to the logical and of
    [cnf1] and [cnf2]. *)
and cnf_and (cnf1 : cnf_formula) (cnf2 : cnf_formula) : cnf_formula =
  cnf1 @ cnf2

(** [cnf_or cnf1 cnf2] returns a CNF formula equivalent to the logical or of
    [cnf1] and [cnf2]. *)
and cnf_or (cnf1 : cnf_formula) (cnf2 : cnf_formula) : cnf_formula =
  if List.is_empty cnf1 then cnf1
  else if List.is_empty cnf2 then cnf2
  else list_combine (fun l1 l2 -> l1 @ l2) cnf1 cnf2

(* TODO revisit *)
and dnf_factorize ?(acc = []) (cnf : cnf_formula) =
  let rec find_common_opt cnf = function
    | [] -> None
    | x :: xs ->
      if List.for_all (List.exists (fun e -> e = x)) cnf then Some x
      else find_common_opt cnf xs
  in
  match List.sort_uniq List.compare_lengths cnf with
  | [] -> acc
  | [] :: xs -> dnf_factorize ~acc xs
  (* | hd :: [] -> if List.length acc > 0 then list_combine (fun x1 x2 -> x1::x2) hd acc else [hd] *)
  | (_ :: _ as hd) :: _ -> begin
    match find_common_opt cnf hd with
    | None -> acc @ cnf
    | Some lit ->
      let cnf = List.map (List.filter (fun x -> x <> lit)) cnf in
      dnf_factorize ~acc:([ lit ] :: acc) cnf
  end

(** [cnf_neg cnf] returns a CNF formula equivalent to the logical negation of
    [cnf]. *)
and cnf_neg (cnf : cnf_formula) : cnf_formula =
  if List.is_empty cnf then [ [] ]
  else
    dnf_to_cnf
    @@ List.fold_left (fun acc lst -> List.map negate lst :: acc) [] cnf

(** [cnf_of formula] results the result of converting [formula] into CNF. *)
(* and cnf_of (formula : formula) =
  let rec cnf_of formula : cnf_formula =
    match formula with
    | Literal lit -> [ [ lit ] ]
    | Disjunction (left, right) -> begin
      match (left, right) with
      | Literal l, Literal r -> [ [ l; r ] ]
      | Literal v, Disjunction (l, r) | Disjunction (l, r), Literal v ->
        let l_cnf = cnf_of l
        and r_cnf = cnf_of r in
        cnf_or [ [ v ] ] (cnf_or l_cnf r_cnf)
      | Literal v, Conjunction (l, r) | Conjunction (l, r), Literal v ->
        let l_cnf = cnf_of l
        and r_cnf = cnf_of r in
        cnf_or [ [ v ] ] (l_cnf @ r_cnf)
      | _ ->
        let l_cnf = cnf_of left
        and r_cnf = cnf_of right in
        cnf_or l_cnf r_cnf
    end
    | Conjunction (left, right) -> begin
      match (left, right) with
      | Literal l, Literal r -> [ [ l ]; [ r ] ]
      | Literal v, Disjunction (l, r) | Disjunction (l, r), Literal v ->
        let l_cnf = cnf_of l
        and r_cnf = cnf_of r in
        [ v ] :: cnf_or l_cnf r_cnf
      | Literal v, Conjunction (l, r) | Conjunction (l, r), Literal v ->
        let l_cnf = cnf_of l
        and r_cnf = cnf_of r in
        ([ v ] :: l_cnf) @ r_cnf
      | _ ->
        let l_cnf = cnf_of left
        and r_cnf = cnf_of right in
        l_cnf @ r_cnf
    end
  in
  cnf_of formula |> cnf_simplify *)
