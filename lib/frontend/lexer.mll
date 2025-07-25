{
  open Parser
  open Syntax

  exception UnknownToken of string
  exception Lexical_error of loc * string

  let rec on_unknown_token lexbuf token =
    let char_to_string (c:char) = String.make 1 c in
    let msg = Printf.sprintf "unknown token '%s'" @@ char_to_string token in
    on_error lexbuf msg

  and on_error lexbuf msg =
    let start_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let loc = Location(start_pos, end_pos) in
    raise (Lexical_error (loc, msg))
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let int = '-'? digit+
let id = (alpha) (alpha|digit|'_')*
let whitespace = [' ' '\t']
let newline = "\r\n" | '\r' | '\n'

rule read_token = parse
	| whitespace+   { read_token lexbuf }
	| newline			  { Lexing.new_line lexbuf; read_token lexbuf }
	| "/*"				  { read_block_comment lexbuf }
  | "//"          { read_line_comment lexbuf }
  | "#"           { HASHTAG }
  | "$"           { DOLLAR }
	| "true"        { TRUE } 
	| "false"       { FALSE } 
  (* unguarded dcr relations *)
	| "-->+"        { INCLUDE }
	| "-->%"        { EXCLUDE }
	| "-->*"        { CONDITION }
	| "*-->"        { RESPONSE }
	| "--><>"       { MILESTONE }
	| "-->>"        { SPAWN }
  (* guarded dcr relations - open guard *)
	| "-["          { LGUARD }
	| "*-["         { LGUARD_RESPONSE }
  (* guarded dcr relation - close guard *)
	| "]->+"        { RGUARD_INCLUDE}
	| "]->"         { RGUARD_RESPONSE }
	| "]->%"        { RGUARD_EXCLUDE}
	| "]->*"        { RGUARD_CONDITION}
	| "]-><>"       { RGUARD_MILESTONE}
	| "]->>"        { RGUARD_SPAWN}
  (* @trigger *)
	| "@trigger"    { TRIGGER "@trigger" }
  | "@"           { AT }
	| '\''          { STR (read_string (Buffer.create 20) lexbuf) }
  | '='           { ASSIGN }
	| '+' 				  { PLUS } 
	| '*' 				  { MULT } 
	| '-'				    { MINUS }
	| '~'				    { NEG }
	| "AND" 			  { AND } 
	| "OR" 				  { OR }
	| '<'				    { LESSTHAN }
	| '>'				    { GREATERTHAN }
	| "==" 				  { EQ } 
	| "!=" 				  { NEQ }
	| '.'			  	  { PROP_DEREF }
	| ','			  	  { COMMA }
	| ';'			  	  { SEMICOLON }
	| ':'			  	  { COLON }
	| '{'			  	  { LBRACE }
	| '}'			  	  { RBRACE }
	| '['			  	  { LBRACKET }
	| ']'			  	  { RBRACKET }
	| '(' 				  { LPAR }
	| ')' 				  { RPAR }
	| '?'				    { QUESTION }
	| '%'				    { EXCL }
	| '!'				    { PEND }
	| "String"			{ STRTY }
	| "Integer"			{ INTTY }
	| "Boolean" 		{ BOOLTY }
	| "executed"		{ ID "executed" }
	| "included"		{ ID "included" }
	| "pending"			{ ID "pending" }
	| "value"			  { ID "value" }
  | "@Initiator"  { INITIATOR }
  | "@Receiver"   { RECEIVER }
	| "flows"			  { FLOWS }
	| "Top"         { TOP }
	| "Bot"         { BOT }
	| "->" 		      { ARROW }
  | "as"          { ALIAS }
	| int           { INT (int_of_string @@ Lexing.lexeme lexbuf) }
	| id 				    { ID (Lexing.lexeme lexbuf) }
	| eof 				  { EOL }
	| _ as tk 			{ on_unknown_token lexbuf tk}
	(* | eof 					    { raise End_of_file } *)

and read_string buffer 	= parse
	| '\''          { Buffer.contents buffer } (* returns back to callee *)
	| '\\' 'n'  		{ Buffer.add_char buffer '\n'; read_string buffer lexbuf }
	| '\\' 'r'  		{ Buffer.add_char buffer '\r'; read_string buffer lexbuf }
	| '\\' 't'  		{ Buffer.add_char buffer '\t'; read_string buffer lexbuf }
	| [^'\'' '\\']+	{ Buffer.add_string buffer @@ Lexing.lexeme lexbuf; read_string buffer lexbuf }
	| eof           { on_error lexbuf "Unclosed string literal" }
	| _             { on_error lexbuf @@ Printf.sprintf "Unexpected symbol within string: '%s'" (Lexing.lexeme lexbuf) }

and read_block_comment = parse
	| "*/"					{ read_token lexbuf }
	| eof 					{ on_error lexbuf "Unclosed block-comment" }
	| _   					{ read_block_comment lexbuf }

and read_line_comment = parse
  | newline | eof			{ Lexing.new_line lexbuf; read_token lexbuf }
  | _           	  	{ read_line_comment lexbuf }