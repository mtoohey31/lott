import Lott.DSL.Parser

namespace Lott.DSL

syntax (name := judgementComprehension) "</ " withPosition(Lott.Judgement) " // " ident " ∈ " term " />" : Lott.Judgement

end Lott.DSL
