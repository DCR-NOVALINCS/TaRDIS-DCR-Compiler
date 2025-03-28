%{
open Syntax

  (* TODO remove when participants in communications are properly handled *)
  (* let participant_to_string role params =
     Printf.sprintf "%s(%s)" role @@ String.concat ", " params
     *)

(*
  let ctrl_rels_from_option opt =
    match opt with
    | Some rels -> rels
    | None -> []
    *)

  (*
  let next_uid =
    let counter = ref 0 in
    fun () ->
      incr counter;
      Printf.sprintf "uid_%d" !counter
*)

  let unfold_nested_ctrl_rel_decl nested_ctrl_rel =
    let ids_l, rel, ids_r = nested_ctrl_rel.data in
    let (rel_type, guard_expr') = rel.data in
    let rel_type' = annotate ~loc:rel.loc rel_type in
    let mk_ctrl_relation id1 id2 =
      annotate ~loc:nested_ctrl_rel.loc @@ ControlRelation (id1, guard_expr', id2, rel_type')
    in
    List.map
      (fun id1 -> List.map (fun id2 -> mk_ctrl_relation id1 id2)ids_r) ids_l
    |> List.concat

  and unfold_nested_spawn_rel_decl nested_spawn_rel =
    let ids_l, guard, spawn_program = nested_spawn_rel.data in
    let mk_spawn_relation id =
      annotate ~loc:nested_spawn_rel.loc @@ SpawnRelation (id, guard, spawn_program)
    in
    List.map (fun id1 -> mk_spawn_relation id1 ) ids_l


let default_marking : event_marking' =
  annotate
    { executed' = annotate false
    ; pending' = annotate false
    ; included' = annotate true
    }

let default_marking_pend =
  { executed' = annotate false
  ; pending' = annotate true
  ; included' = annotate true
  }

let default_marking_excl =
  { executed' = annotate false
  ; pending' = annotate false
  ; included' = annotate false
  }

let default_marking_pend_excl =
  { executed' = annotate false
  ; pending' = annotate true
  ; included' = annotate false
  }

(*  TODO cleanup required here *)

(* currently not being used (?) *)

(*
let bot = "Bot"
and top = "Top"
*)

(*
let parse_error s = 
  print_endline s;
  flush stdout
*)

(*
let string_of_position p =
	(string_of_int p.Lexing.pos_lnum) ^":" ^ (string_of_int p.Lexing.pos_cnum)
*)

(*
let raiseError () = 
	let p1 = (Parsing.rhs_start_pos 1) in 
  let p2 = (Parsing.symbol_end_pos()) in
	Parsing.clear_parser ();
  raise (SyntaxError(string_of_position p1, string_of_position p2))
  *)

%}

// declarations
%token EOL
// type literals
%token <int> INT
%token <string> STR
// value literals
%token TRUE FALSE
%token <string> ID
// primitive types
%token STRTY INTTY BOOLTY
// delimiters
%token LPAR RPAR LBRACE RBRACE LBRACKET RBRACKET 
// separators
%token COMMA COLON SEMICOLON
// assignment
%token ASSIGN
// binary ops
%token PLUS MULT AND OR EQ NEQ LESSTHAN GREATERTHAN
// unary ops
%token NEG MINUS
// ====== DCR
// dcr literals
%token <string> TRIGGER 
%token EXCL PEND
// (unguarded) dcr relations
%token INCLUDE EXCLUDE CONDITION RESPONSE MILESTONE SPAWN
// (guarded) dcr relations - guard opening (left)
%token LGUARD LGUARD_RESPONSE
// (guarded) dcr relations - guard closing
%token RGUARD_INCLUDE RGUARD_EXCLUDE RGUARD_CONDITION RGUARD_RESPONSE RGUARD_MILESTONE RGUARD_SPAWN
// information flow
%token FLOWS TOP BOT
// userset expressions
%token INITIATOR RECEIVER
// misc
%token ALIAS HASHTAG AT QUESTION ARROW PROP_DEREF
// %token PIPE // TODO revise utility
// %token UDRSCR // TODO revise utility
%nonassoc NEG
%nonassoc PROP_DEREF 

%start main 

%type <program> main

%% /* rules */ 

main:
  plain_program EOL                                                                               { $1 }
;


// program: mark_loc_ty(plain_program) {$1}
      // let {events; relations} = spawn_prog in
plain_program:
    roles = terminated(plain_value_dep_role_decls, SEMICOLON);
    security_lattice = terminated(plain_flow_decl_list, SEMICOLON);
    spawn_program = plain_program_spawn;
    { 
      {roles
      ; security_lattice
      ; spawn_program
      } 
    }
;


// value_dependent_roles : type_expr parameterisable_label list
plain_value_dep_role_decls:
|  decls=nonempty_list(value_dep_role_decl)    {decls}
;

// <id> [ '(' <param> [; <param>]* ')' ]
// type_expr parameterisable_label' = identifier * 'a named_param list
value_dep_role_decl: mark_loc_ty(plain_value_dep_role_decl) {$1}
plain_value_dep_role_decl:
| id=id                              {(id, [])}
| id=id; LPAR; params=separated_nonempty_list(SEMICOLON, value_dep_role_param); RPAR  {(id, params)}
;

// <id>:<type_expr>
value_dep_role_param: mark_loc_ty(plain_value_dep_role_param) {$1}
plain_value_dep_role_param:
|  id=id; COLON; ty=type_expr         {(id,ty)}
;

// plain_security_class_decl_section:
//   decls=nonempty_list(security_class_decl)    {decls}
// ;

// security_class_decl: mark_loc_ty(plain_security_class_decl) {$1}
// plain_security_class_decl:
//   id=id                              {PlainSCDecl(id)}
// | id=id; LPAR; ty=type_expr; RPAR    {ParametrisedSCDecl(id, ty)}
// ;

plain_flow_decl_list:
  | flows = nonempty_list(flow_decl) { flows }

flow_decl: mark_loc_ty(plain_flow_decl) {$1}
plain_flow_decl:
  separated_pair(id, FLOWS, id)                { $1 }
;





plain_event_decl_list:
  | events = nonempty_list(event_decl) { events }

event_decl: mark_loc_ty(plain_event_decl) {$1}
plain_event_decl:
  // marking declared in abbreviated form (as a prefix, one of !, %, !%, %!)
  | marking = marking_prefix;
    info = delimited(LPAR, event_info , RPAR); 
    security_level = delimited(LPAR, security_level, RPAR);
    data_expr = delimited(LBRACKET, data_expr, RBRACKET);
    participants = delimited(LBRACKET, participants_expr ,RBRACKET)
    // kind = delimited(LBRACKET, kind_expr, RBRACKET);
        { {info; security_level; data_expr; participants; marking} }
        // { {info; security_level; data_expr; participants; marking; kind} }
        // { {info; security_level; data_expr; marking; kind} }
        // { {info; access_ctrl=(fst sec.data); security_level; data_expr; marking; kind} }
  // (optionally) marking declared in extended form
  | info = delimited(LPAR, event_info , RPAR); 
    security_level = delimited(LPAR, security_level, RPAR);
    data_expr = delimited(LBRACKET, data_expr, RBRACKET);
    participants = delimited(LBRACKET, participants_expr ,RBRACKET)
    marking = delimited(LBRACE,node_marking, RBRACE)?;
    // kind = delimited(LBRACKET, kind_expr, RBRACKET);
      { {info; security_level; data_expr; participants; marking=Option.value ~default:default_marking marking} }
      // { {info; security_level; data_expr; participants; marking=Option.value ~default:default_marking marking; kind} }
      // { {info; security_level; data_expr; marking=Option.value ~default:default_marking marking; kind} }
      // { {info; access_ctrl=(fst sec.data); security_level; data_expr; marking=Option.value ~default:default_marking marking; kind} }
;


marking_prefix: mark_loc_ty(plain_marking_prefix) {$1}
plain_marking_prefix:
  | EXCL                      { default_marking_excl }
  | PEND                      { default_marking_pend }
  | EXCL PEND | PEND EXCL     { default_marking_pend_excl }
;

event_info: mark_loc_ty(plain_event_info) {$1}
plain_event_info:
  | separated_pair(id, COLON, id)    { $1 }
;

security_level: mark_loc_ty(plain_security_level) {$1}
plain_security_level:
| sec_level=separated_nonempty_list(COMMA, security_label)    {sec_level}
;

security_label: mark_loc_ty(plain_security_label) { $1 }
plain_security_label:
| id                                                             {($1, [])}
| id=id; params=delimited(LPAR, plain_sec_label_params, RPAR)    {(id, params)}
;

plain_sec_label_params:
| separated_nonempty_list(SEMICOLON, sec_label_param)   {$1}
;

sec_label_param: mark_loc_ty(plain_sec_label_param) {$1}
plain_sec_label_param:
|  id=id; COLON; value=sec_label_param_val         {(id,value)}
;

sec_label_param_val: mark_loc_ty(plain_sec_label_param_val) {$1}
plain_sec_label_param_val:
| TOP                         {Top}
| BOT                         {Bot}
| fact                        {Parameterised($1)}
;



plain_ctrl_relation_decl_list:
  | rels= nonempty_list(plain_nested_relation_decls)       { List.flatten rels }
;

plain_nested_relation_decls:
  | nested_ctrl_rel_decl    {unfold_nested_ctrl_rel_decl $1}
  | nested_spawn_rel_decl   {unfold_nested_spawn_rel_decl $1}
;

nested_ctrl_rel_decl: mark_loc_ty(plain_nested_ctrl_rel_decl) {$1}
plain_nested_ctrl_rel_decl:
  | ids_l = separated_nonempty_list(COMMA, id);
    rel_type = ctrl_relation_type;
    ids_r =separated_nonempty_list(COMMA, id)              {(ids_l, rel_type, ids_r)}
;

nested_spawn_rel_decl: mark_loc_ty(plain_nested_spawn_rel_decl) {$1}
plain_nested_spawn_rel_decl:
  | ids_l = separated_nonempty_list(COMMA, id);
    rel_type = spawn_relation_type;
    prog=delimited(LBRACE, plain_program_spawn, RBRACE)    {(ids_l, rel_type, prog)}
;

ctrl_relation_type: mark_loc_ty(plain_ctrl_relation_type) {$1}
plain_ctrl_relation_type:
  | INCLUDE                                          {(Include, annotate True)}
  | EXCLUDE                                          {(Exclude, annotate True)}
  | CONDITION                                        {(Condition, annotate True)}
  | RESPONSE                                         {(Response, annotate True)}
  | MILESTONE                                        {(Milestone, annotate True)}
  | LGUARD; expr=expr; RGUARD_INCLUDE                {(Include, expr)}
  | LGUARD; expr=expr; RGUARD_EXCLUDE                {(Exclude, expr)}
  | LGUARD; expr=expr; RGUARD_CONDITION              {(Condition, expr)}
  | LGUARD_RESPONSE; expr=expr; RGUARD_RESPONSE      {(Response, expr)}
  | LGUARD; expr=expr; RGUARD_MILESTONE              {(Milestone, expr)}
;

spawn_relation_type: mark_loc_ty(plain_spawn_relation_type) {$1}
plain_spawn_relation_type:
  | SPAWN                                                 {True}
  | LGUARD; expr=plain_expr; RGUARD_SPAWN                 {expr}
;



// ======= event.data_expr

data_expr: mark_loc_ty(plain_data_expr) {$1}
plain_data_expr:
| input_expr = preceded(QUESTION, input_expr)      { Input(input_expr) }
| computation_expr = expr                          { Computation(computation_expr) }
;

input_expr: mark_loc_ty_ty(plain_input_expr) { $1 }
plain_input_expr:
  |                                       { UnitTy }
  | preceded(COLON, plain_type_expr)      { $1 }
;


// ======= event.participants

participants_expr: mark_loc_ty(plain_participants_expr) {$1}
plain_participants_expr:
| user_set_expr                                                   { Local($1) }
| pair=separated_pair(user_set_expr, ARROW, separated_nonempty_list(COMMA, user_set_expr))  { Interaction(fst pair, snd pair) }
;

user_set_expr: mark_loc_ty(plain_user_set_expr) {$1}
plain_user_set_expr:
| user_set_role_expr                              {RoleExpr($1)} 
| INITIATOR; event_id=delimited(LPAR, id, RPAR)    {Initiator(event_id)}
| RECEIVER; event_id=delimited(LPAR, id, RPAR)    {Receiver(event_id)}
;

user_set_role_expr: mark_loc_ty(plain_user_set_role_expr) {$1}
plain_user_set_role_expr:
| role=id                                                       {(role, [])}
| role=id; params=delimited(LPAR, separated_nonempty_list(SEMICOLON, user_set_role_expr_param) ,RPAR)   {(role,params)}   
;


user_set_role_expr_param: mark_loc_ty(plain_user_set_role_expr_param) {$1}
plain_user_set_role_expr_param:
| separated_pair(id, ASSIGN, user_set_role_expr_param_val)          {$1}
| HASHTAG; id=id; alias=option(user_set_role_expr_param_alias)      
  // {(id, annotate ~loc:(id.loc) (RuntimeValue(alias)))}
  {(id, annotate ~loc:(id.loc) (Option.fold ~none:Any ~some:(fun alias -> RuntimeValue(Some alias)) alias))}
;

user_set_role_expr_param_alias:
| ALIAS; alias=id     {alias}
;

// user_set_param_val'
user_set_role_expr_param_val: mark_loc_ty(plain_user_set_role_expr_param_val) {$1}
plain_user_set_role_expr_param_val:
| user_set_role_expr_param_val_fact        {Expr($1)}
| MULT              {Any}
| expr = preceded(AT, id)                  { Alias(expr) }
;

user_set_role_expr_param_val_fact: mark_loc_ty(plain_user_set_role_expr_param_val_fact) { $1 }
plain_user_set_role_expr_param_val_fact:
| TRUE                                     { True }
| FALSE                                    { False }
| INT                                      { IntLit($1) }
| STR                                      { StringLit($1) }
| id                                       { EventRef($1) } 
| TRIGGER                                  { Trigger($1) }
| expr = user_set_role_expr_param_val_fact; PROP_DEREF; prop = id      { PropDeref(expr, prop) }
;

node_marking: mark_loc_ty(plain_node_marking) {$1}
plain_node_marking:
  | exec = bool; COMMA; pend = bool; COMMA; inc = bool    { {executed' = exec; pending' = pend; included' = inc} }
;

// kind_expr: mark_loc_ty(plain_kind_expr) {$1}
// plain_kind_expr:   
// | initiator = participant                                 { Action initiator }
// | initiator = participant; ARROW;
//    receivers=separated_nonempty_list(COMMA, participant)  { UserInteraction (initiator, receivers) }
// ;

// participant: mark_loc_ty(plain_participant) {$1}
// plain_participant:
// | ID                                                                         {$1}
// | role=ID; params=delimited(LPAR, separated_nonempty_list(COMMA, plain_participant_param), RPAR)  {participant_to_string role params}
// | INITIATOR; event_id=delimited(LPAR id, RPAR)    {Initiator(event_id)}
// ;

// plain_participant_param:
// | INT     {string_of_int $1}
// | STR      {$1}
;

type_expr: mark_loc_ty_ty(plain_type_expr) {$1}
plain_type_expr:
| STRTY                                                                                   { StringTy }
| INTTY                                                                                   { IntTy    }
| BOOLTY                                                                                  { BoolTy   }
| plain_id                                                                                { EventTy($1) }
| delimited(LBRACE, separated_nonempty_list(SEMICOLON, record_type_field), RBRACE)            { RecordTy($1) }
// TODO [revisit] it may still be useful (w/ primitive types), e.g., Int(x | x > 10), String(s | s != '')
// | LBRACE ID COLON type_expr BAR expr RBRACE        { RefinedTy($2,$4,$6) }
;

record_type_field: mark_loc_ty(plain_record_type_field) {$1}
plain_record_type_field:
| name=id; COLON; value=type_expr     {(name, value)}
;

plain_program_spawn:
    events = plain_event_decl_list;
    ctrl_rels = preceded(SEMICOLON, plain_ctrl_relation_decl_list)?;
      { {events; relations=Option.value ~default:[] ctrl_rels} }
;

expr: mark_loc_ty(plain_expr) { $1 }
plain_expr:
|  plain_orop                                  { $1 }
;

orop: mark_loc_ty(plain_orop) { $1 }
plain_orop:
| orop OR andop                                { BinaryOp($1,$3, Or) }
| plain_andop                                  { $1 }
;

andop: mark_loc_ty(plain_andop) { $1 }
plain_andop:
| andop AND compareop                          { BinaryOp($1,$3,And) }
| plain_compareop                              { $1 }
;

compareop: mark_loc_ty(plain_compareop) { $1 }
plain_compareop:
| compareop EQ arith                           { BinaryOp($1,$3,Eq) }
| compareop NEQ arith                          { BinaryOp($1,$3,NotEq) }
| compareop GREATERTHAN arith                  { BinaryOp($1,$3,GreaterThan) }
| compareop LESSTHAN arith                     { BinaryOp($1,$3,LessThan) }
// | plain_event_ref                                {$1}
| plain_arith                                  { $1 } 
;

// event_ref: mark_loc_ty(plain_event_ref) { $1 }
// plain_event_ref:
// | id                                           { EventRef($1) } 
// | plain_arith                                  { $1 } 
// ;


arith: mark_loc_ty(plain_arith) { $1 }
plain_arith: 
| arith PLUS term                              { BinaryOp($1,$3,Add) }
| plain_term                                   { $1          }
;

term: mark_loc_ty(plain_term) { $1 }
plain_term: 
| term MULT fact                               { BinaryOp($1,$3,Mult) }
| plain_fact                                   { $1 }
;

fact: mark_loc_ty(plain_fact) { $1 }
plain_fact:
| expr = preceded(NEG, fact)                                                      { UnaryOp(expr, Negation) }
| expr = preceded(MINUS, fact)                                                    { UnaryOp(expr, Minus) }
| TRUE                                                                            { True }
| FALSE                                                                           { False }
| INT                                                                             { IntLit($1) }
| STR                                                                             { StringLit($1) }
| id                                                                              { EventRef($1) } 
| TRIGGER                                                                         { Trigger($1) }
| delimited(LBRACE, separated_nonempty_list(SEMICOLON, record_field), RBRACE)         { Record($1) }
| expr = fact; PROP_DEREF; prop = id;                                             { PropDeref(expr, prop) }
;

bool: mark_loc_ty(plain_bool) { $1 }
plain_bool:
  | TRUE        { true }
  | FALSE       { false }
;

record_field: mark_loc_ty(plain_record_field) {$1}
plain_record_field:
| name=id; ASSIGN; value=expr               {(name, value)}
;

id: mark_loc_ty(plain_id) {$1}
plain_id:
  | id=ID  { id }
;

mark_loc_ty(X):
  x = X
  { annotate ~loc:(Location($startpos, $endpos)) x}
;

mark_loc_ty_ty(X):
  x = X
  { annotate ~loc:(Location($startpos, $endpos)) ~ty:(Some{t_expr=x; is_const=false}) x}
;
%%