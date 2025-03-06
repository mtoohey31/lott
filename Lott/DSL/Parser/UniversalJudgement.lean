import Lott.DSL.Parser

namespace Lott.DSL

open Lean.Parser.Term

syntax (name := universalJudgement) "∀ " (ppSpace (binderIdent <|> bracketedBinder))+ optType ", " withPosition(Lott.Judgement) : Lott.Judgement

syntax (name := universalPredJudgement) "∀ " ident binderPred ", " withPosition(Lott.Judgement) : Lott.Judgement

end Lott.DSL
