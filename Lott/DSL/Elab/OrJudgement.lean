import Lott.DSL.Elab.Basic
import Lott.DSL.Parser.OrJudgement

namespace Lott.DSL.Elab

open Lean.Elab

@[lott_term_elab Lott.DSL.orJudgement]
private
def orJudgementTermElab : TermElab := fun _ stx => do
  let `(Lott.Judgement| $j₀:Lott.Judgement ∨ $j₁:Lott.Judgement) := stx | throwUnsupportedSyntax
  let stx' ← ``([[$j₀:Lott.Judgement]] ∨ [[$j₁:Lott.Judgement]])
  Lean.Elab.Term.elabTerm stx' none

end Lott.DSL.Elab
