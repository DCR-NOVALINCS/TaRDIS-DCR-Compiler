module Choreo = Frontend.Syntax
module StringMap = Map.Make (String)

(* TODO [odoc] *)

module CnfRole : sig
  exception Invalid_arguments of string

  type t =
    { label : Choreo.identifier
    ; param_types : Choreo.type_expr StringMap.t
    ; encoding : Sat.cnf_formula
    }

  (** Return a CnfRole.t reflecting the specified role_decl **)
  val of_role_decl : role_decl':Choreo.value_dep_role_decl' -> t

  (** Return a CnfRole.t reflecting the union of two cnf-encoded roles
      (encoding-only, no solving). Requires equally-labelled roles. **)
  val union : t -> t -> t

  (** Return a CnfRole.t reflecting the intersection of two cnf-encoded roles
      (encoding-only, no solving). Requires equally-labelled roles. **)
  val of_intersection : t -> t -> t

  val to_string : ?indent:string -> ?abbreviated:bool -> t -> string

  val resolve_role_diff : t -> t -> t option

  val complement : t -> t

  val resolve_role_complement : t -> t option

  val role_union : t -> t -> t

  val all_sat : t -> t list

  val resolve_role_union : t -> t -> t option

  val resolve_role_intersection : t -> t -> t option

  val is_subrole : t -> t -> bool
end = struct
  open Choreo
  open Sat

  exception Invalid_arguments of string

  type t =
    { label : identifier
    ; param_types : type_expr StringMap.t
    ; encoding : cnf_formula
    }

  and cnf_role = t

  let of_role_decl ~(role_decl' : value_dep_role_decl') =
    let label', params = role_decl'.data in
    let param_types =
      List.fold_left
        (fun constrained_role_params named_param ->
          let param_name', param_val' = named_param.data in
          let param_ty = (Option.get !(param_val'.ty)).t_expr in
          StringMap.add param_name'.data param_ty constrained_role_params)
        StringMap.empty
        params
    in
    { label = label'.data; param_types; encoding = [] }

  let all_sat (t : t) =
    List.map
      (fun encoding -> { t with encoding })
      (cnf_all_sat_solve t.encoding)

  let union (left : cnf_role) (right : cnf_role) : cnf_role =
    if left.label <> right.label then
      raise (Invalid_arguments "Role union requires equally-labelled roles.")
    else
      let r_except_l = cnf_and right.encoding (cnf_neg left.encoding) in
      { left with encoding = cnf_or left.encoding r_except_l }

  and of_intersection (left : cnf_role) (right : cnf_role) : t =
    if left.label <> right.label then
      raise
        (Invalid_arguments "Role intersection requires equally-labelled roles.")
    else { left with encoding = cnf_and left.encoding right.encoding }

  let to_string ?(indent = "") ?(abbreviated = true)
      ({ label; param_types; encoding } as _t : t) =
    let sprintf = Printf.sprintf in
    let unparse_ty_expr t = Frontend.Unparser.unparse_type_expr (annotate t) in
    StringMap.bindings param_types
    |> List.map (fun (label, ty) -> sprintf "%s:%s" label (unparse_ty_expr ty))
    |> String.concat "; "
    |> fun params ->
    if abbreviated then
      sprintf "%s%s%s" indent label (unparse_cnf_formula encoding)
    else sprintf "%s%s(%s)%s" indent label params (unparse_cnf_formula encoding)

  let rec resolve_role_diff (l_role : cnf_role) (r_role : cnf_role) :
      cnf_role option =
    if l_role.label <> r_role.label then Some l_role
    else
      match resolve_role_intersection l_role r_role with
      | None -> Some l_role
      | Some { encoding; _ } ->
        Option.bind
          (cnf_sat_solve @@ cnf_and l_role.encoding (cnf_neg encoding))
          (fun encoding -> Some { l_role with encoding })

  and complement (role : cnf_role) : cnf_role =
    { role with encoding = cnf_neg role.encoding }

  and resolve_role_complement (role : cnf_role) : cnf_role option =
    Option.bind
      (cnf_sat_solve @@ cnf_neg role.encoding)
      (fun encoding -> Some { role with encoding })

  (* Returns a role encoding the role union of l_role and r_role - not solving,
     may not be feasible *)
  and role_union l_role r_role =
    if l_role.label <> r_role.label then
      raise (Invalid_arguments "Role union requires arguments of the same role")
    else { l_role with encoding = cnf_or l_role.encoding r_role.encoding }

  and resolve_role_union (l_role : cnf_role) (r_role : cnf_role) :
      cnf_role option =
    if l_role.label <> r_role.label then
      raise (Invalid_arguments "Role union requires arguments of the same role")
    else if List.is_empty l_role.encoding || List.is_empty r_role.encoding then
      (* union is universe *)
      Some { l_role with encoding = [] }
    else
      Option.bind
        (cnf_sat_solve (cnf_or l_role.encoding r_role.encoding))
        (fun encoding -> Some { l_role with encoding })

  and resolve_role_intersection (left : cnf_role) (right : cnf_role) :
      cnf_role option =
    if left.label <> right.label then None
    else
      Option.bind
        (cnf_sat_solve @@ cnf_and left.encoding right.encoding)
        (fun encoding -> Some { left with encoding })

  and is_subrole (left : cnf_role) (right : cnf_role) : bool =
    (* A \in B <=> (A \ intersect ~B) = \empty *)
    if left.label <> right.label then false
    else
      let res =
        Option.fold
          ~none:true
          ~some:(fun neg_right ->
            Option.is_none @@ resolve_role_intersection left neg_right)
          (resolve_role_complement right)
      in
      res

  let sat_solve (role : cnf_role) : cnf_role option =
    Option.bind (cnf_sat_solve role.encoding) (fun encoding ->
        Some { role with encoding })

  let sat_solve_disjoint (role : cnf_role) : cnf_role list =
    List.map
      (fun encoding -> { role with encoding })
      (cnf_all_sat_solve role.encoding)
end

module CnfUserset : sig
  type t = CnfRole.t StringMap.t

  val of_role_decls : Choreo.value_dep_role_decl' list -> t

  val empty : t

  val singleton : CnfRole.t -> t

  val is_empty : t -> bool

  val includes : CnfRole.t -> t -> bool

  val is_subset : t -> t -> bool

  (** Return a CnfGroup.t reflecting the union of two cnf-encoded roles
      (encoding-only, no solving). **)
  val add_role : t -> CnfRole.t -> t

  val exclude_role : t -> CnfRole.t -> t
  (* val of_union : t -> t -> t *)

  (* val resolve_intersection : ?unique_syms:bool -> t -> t -> t *)
  val resolve_intersection : t -> t -> t

  val intersects : t -> t -> bool

  val to_string : ?indent:string -> t -> string

  val to_list : t -> CnfRole.t list
end = struct
  open Choreo

  type t = CnfRole.t StringMap.t

  let empty = StringMap.empty

  let of_role_decls (role_decls : Choreo.value_dep_role_decl' list) =
    List.map
      (fun role_decl' ->
        ((fst role_decl'.data).data, CnfRole.of_role_decl ~role_decl'))
      role_decls
    |> StringMap.of_list

  let singleton cnf_role = StringMap.singleton cnf_role.CnfRole.label cnf_role

  let is_empty (t : t) = StringMap.is_empty t

  let add_role (t : t) ({ label; _ } as cnf_role : CnfRole.t) =
    Option.fold
      ~none:(StringMap.add label cnf_role t)
      ~some:(fun prev -> StringMap.add label (CnfRole.union prev cnf_role) t)
      (StringMap.find_opt label t)

  let union (left : t) (right : t) =
    StringMap.union (fun _ v1 v2 -> Some (CnfRole.union v1 v2)) left right

  let resolve_intersection (left : t) (right : t) : t =
    StringMap.merge
      (fun _ left right ->
        match (left, right) with
        | Some l, Some r -> CnfRole.resolve_role_intersection l r
        | _ -> None)
      left
      right

  let resolve_union (left : t) (right : t) : t =
    StringMap.union
      (fun _ left right -> CnfRole.resolve_role_union left right)
      left
      right

  let intersects (left : t) (right : t) : bool =
    StringMap.exists
      (fun label left ->
        Option.fold
          ~none:false
          ~some:(fun right ->
            Option.fold
              ~none:false
              ~some:(fun _ -> true)
              (CnfRole.resolve_role_intersection left right))
          (StringMap.find_opt label right))
      left

  (* checks whether role is included in t *)
  let rec includes (role : CnfRole.t) (t : t) : bool =
    Option.fold
      ~none:false
      ~some:(fun curr ->
        CnfRole.is_subrole role curr)
      (StringMap.find_opt role.label t)

  and is_subset (left : t) (right : t) : bool =
    StringMap.for_all (fun _ left -> includes left right) left

  let exclude_role (t : t) (role : CnfRole.t) =
    let { label; _ } : CnfRole.t = role in
    match StringMap.find_opt label t with
    | None -> t
    | Some prev -> begin
      match CnfRole.resolve_role_diff prev role with
      | None -> StringMap.remove label t
      | Some role ->
        StringMap.add label role t
    end

  let to_list (t : t) = StringMap.bindings t |> List.map snd

  let to_string ?(indent = "") cnf_group =
    List.map
      (fun (_, cnf_role) -> CnfRole.to_string ~indent cnf_role)
      (StringMap.bindings cnf_group)
    |> String.concat "\n"
end
