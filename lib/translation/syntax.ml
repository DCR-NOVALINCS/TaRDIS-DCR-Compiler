(* open Utils.Env

type binary_op = expr * expr * binary_op_type
and binary_op_type =
  | Add
  | Mult
  | Eq
  | NotEq
  | GreaterThan
  | LessThan
  | And
  | Or

and unary_op_type =
  | Minus
  | Negation

and unary_op = expr * unary_op_type

and expr =
  | Unit
  | Boolean of bool 
  | Integer of int
  | String of string
  | ParenthesisExp of expr
  | BinaryOp of expr * expr * binary_op_type
  | UnaryOp of expr * unary_op_type
  | Identifier of string
  | Trigger
  | PropDeref of expr * string
  | List of expr list
  | Record of record_field list


(* type expr =
  | Unit
  | Boolean of bool 
  | Integer of int
  | String of string
  | Record of record_field list
  | ParenthesisExp of expr
  | Add of expr * expr
  (* | Subtract of expr * expr *)
  | Mult of expr * expr
  | Eq of expr * expr
  | NotEq of expr * expr
  | GreaterThan of expr * expr
  | LessThan of expr * expr
  | And of expr * expr
  | Or of expr * expr
  | Minus of expr
  | NotBool of expr
  | EventId of string
  | Trigger
  | PropDeref of expr * string
  | List of expr list *)

and record_field = {
  field_name : string;
  field_value : expr;
}

and type_expr =
  | UnitType
  | StringType
  | IntType
  | BoolType
  | RecordType of record_field_type list

and record_field_type = {
  field_name : string;
  field_ty : type_expr;
}

and event_class =
  | InputAction of type_expr * string
  | OutputAction of expr * type_expr * string
  (* | SendOperation of expr * type_expr * string * string list *)
  | InputSendOperation of type_expr * string * string list
  | OutputSendOperation of expr * type_expr * string * string list
  | ReceiveOperation of type_expr * string * string


and included = bool
and pending = bool
and executed = bool

and event_marking = {
  included : included;
  pending : pending;
  executed : executed;
}

and event_op = {
  event_class : event_class;
  event_id: string;
  event_label : string;
  event_marking : event_marking;
}

and relation_type = 
  | Include
  | Exclude
  | Response
  | Condition
  | Milestone

(* Context related types*)

type context = {
  events : event_op list;
  relations: (relation_type * string * string) list;
  env: event_op t;
}

and projection_context = (string * context) list

let empty_projection_context = []

let empty_context = {
  events = [];
  relations = [];
  env = Utils.Env.empty;
}

(* Helper functions *)
 
(* String functions *)

let rec string_of_expr expr = 
  match expr with 
  | Unit -> failwith "Unit type not supported"
  | Boolean b -> string_of_bool b
  | Integer i -> string_of_int i
  | String s -> s
  | Record r -> 
    let fields = List.map (fun {field_name; field_value} -> field_name ^ ": " ^ (string_of_expr field_value)) r in
    Printf.sprintf "{%s}" (String.concat ", " fields)
  | ParenthesisExp e -> Printf.sprintf "(%s)" (string_of_expr e)
  | BinaryOp (e1, e2, Add) -> Printf.sprintf "%s + %s" (string_of_expr e1) (string_of_expr e2)
  | BinaryOp (e1, e2, Mult) -> Printf.sprintf "%s * %s" (string_of_expr e1) (string_of_expr e2)
  | BinaryOp(e1, e2, Eq) -> Printf.sprintf "%s == %s" (string_of_expr e1) (string_of_expr e2)
  | BinaryOp (e1, e2, NotEq) -> Printf.sprintf "%s != %s" (string_of_expr e1) (string_of_expr e2)
  | BinaryOp (e1, e2, GreaterThan) -> Printf.sprintf "%s > %s" (string_of_expr e1) (string_of_expr e2)
  | BinaryOp (e1, e2, LessThan) -> Printf.sprintf "%s < %s" (string_of_expr e1) (string_of_expr e2)
  | BinaryOp (e1, e2, And) -> Printf.sprintf "%s && %s" (string_of_expr e1) (string_of_expr e2)
  | BinaryOp (e1, e2, Or) -> Printf.sprintf "%s || %s" (string_of_expr e1) (string_of_expr e2)
  | UnaryOp (e, Minus) -> Printf.sprintf "-%s" (string_of_expr e)
  | UnaryOp (e, Negation) -> Printf.sprintf "!%s" (string_of_expr e)
  | Identifier s -> s
  | Trigger -> "trigger"
  | PropDeref (e, s) -> Printf.sprintf "%s.%s" (string_of_expr e) s
  | List l -> Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_expr l))

let rec string_of_type_expr ty = 
  match ty with
  | UnitType -> "UnitType.TYPE"
  | StringType -> "StringType.TYPE"
  | IntType -> "IntType.TYPE"
  | BoolType -> "BooleanType.TYPE"
  | RecordType fields -> 
    let fields_str = List.fold_left (fun acc {field_name; field_ty} -> 
      let field_ty_str = string_of_type_expr field_ty in
      String.concat ", " ["\"" ^ field_name ^ "\""; field_ty_str] :: acc
    ) [] fields in
    Printf.sprintf "RecordType.newBuilder()%s.build()" @@
    String.concat "" (List.map (fun str_param -> Printf.sprintf ".add(%s)" str_param) fields_str)


     *)