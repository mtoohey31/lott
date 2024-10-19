import Lott.DSL.Elab.Basic
import Lott.DSL.Parser.UniversalJudgement

namespace Lott.DSL.Elab

open Lean.Elab

@[lott_term_elab Lott.DSL.universalJudgement]
private
def universalJudgementTermElab : TermElab := fun _ stx => do
  let `(Lott.Judgement| ∀ $i $[$binderPred?]?, $«judgement»:Lott.Judgement) := stx
    | throwUnsupportedSyntax
  let stx' ← if let some bp := binderPred? then
      ``(∀ $i:ident, satisfies_binder_pred% $i $bp → [[$«judgement»:Lott.Judgement]])
    else
      ``(∀ $i:ident, [[$«judgement»:Lott.Judgement]])
  Lean.Elab.Term.elabTerm stx' none

end Lott.DSL.Elab

