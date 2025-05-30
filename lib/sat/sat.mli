module Choreo : module type of Frontend.Syntax

type param_value =
  | BoolLit of bool
  | IntLit of int
  | StringLit of string

and cnf_bool_constraint =
  | CnfSymEq of Choreo.identifier * Choreo.identifier
  | CnfEq of Choreo.identifier * param_value

and literal =
  | Positive of cnf_bool_constraint
  | Negative of cnf_bool_constraint

and cnf_clause = literal list

and cnf_formula = cnf_clause list

val unparse_cnf_formula : cnf_formula -> string

val cnf_clause_compare : cnf_clause -> cnf_clause -> int

val cnf_sat_solve : cnf_formula -> cnf_formula option

val cnf_all_sat_solve : cnf_formula -> cnf_formula list

val cnf_entails : cnf_formula -> cnf_clause -> bool

val cnf_and : cnf_formula -> cnf_formula -> cnf_formula

val cnf_or : cnf_formula -> cnf_formula -> cnf_formula

val cnf_neg : cnf_formula -> cnf_formula
