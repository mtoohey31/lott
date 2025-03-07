import Lott.Parser

namespace Lott

open Lean.Parser
open Lean.Parser.Term

syntax (name := judgementComprehension) "</ " withPosition(Lott.Judgement) " // " term " in " term " />" : Lott.Judgement

end Lott
