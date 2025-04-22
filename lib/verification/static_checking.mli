open Frontend.Syntax
open Utils

exception Typecheck_IFC_error of string

val check_static_information_security : program -> ( program,(loc * string) list )result
