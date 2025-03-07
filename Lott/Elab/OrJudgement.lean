import Lott.Elab.Basic
import Lott.Parser.OrJudgement

namespace Lott.Elab

open Lean.Elab

@[lott_term_elab Lott.orJudgement]
private
def orJudgementTermElab : TermElab := fun _ stx => do
  let `(Lott.Judgement| $j₀:Lott.Judgement ∨ $j₁:Lott.Judgement) := stx | throwUnsupportedSyntax
  let stx' ← ``([[$j₀:Lott.Judgement]] ∨ [[$j₁:Lott.Judgement]])
  Lean.Elab.Term.elabTerm stx' none

end Lott.Elab
