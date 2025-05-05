module TreeMap : module type of Map.Make (String)
open Frontend.Syntax
open Utils

exception Typecheck_IFC_error of string


val check_static_information_security : program -> ( expr list list TreeMap.t,(loc * string) list )result
