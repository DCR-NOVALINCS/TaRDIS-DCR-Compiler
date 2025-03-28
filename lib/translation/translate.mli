(* open Syntax
open Tardis.Syntax
open Utils.Result
open Utils.Env

(**
  [translate [(role1, [(events1, relations1); ...; (eventsN, relationsN)]);...; (roleN, [(events1, relations1); ...; (eventsN, relationsN)])]]
  translates a list of pairs containing its [role_name] and its events and relations into a list of Babel contexts with the role name as key.
*)
val translate :
    (string * (projected_event' list * relation' list)) list -> 
    (string * context) list   *)