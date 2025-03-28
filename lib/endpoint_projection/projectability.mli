module Choreo : module type of Frontend.Syntax

val check : Choreo.program ->
  Verification.Typing.typecheck_result ->
  (unit, (Choreo.loc * Choreo.element_uid) list) result