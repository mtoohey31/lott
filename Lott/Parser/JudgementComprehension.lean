import Lott.Parser

namespace Lott

open Lean.Parser
open Lean.Parser.Term

syntax (name := judgementComprehension) "</ " withPosition(Lott.Judgement) " // " (strLitTexConfig)? term " in " term " notex"? " />" : Lott.Judgement

end Lott
