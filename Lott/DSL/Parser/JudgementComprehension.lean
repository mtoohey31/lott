import Lott.DSL.Parser

namespace Lott.DSL

open Lean.Parser
open Lean.Parser.Term

syntax (name := judgementComprehension) "</ " withPosition(Lott.Judgement) " // " term " in " term " />" : Lott.Judgement

end Lott.DSL
