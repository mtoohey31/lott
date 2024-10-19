import Lott.DSL.Parser

namespace Lott.DSL

syntax (name := universalJudgement) "∀ " ident (binderPred)? ", " withPosition(Lott.Judgement) : Lott.Judgement

end Lott.DSL
