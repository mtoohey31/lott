import Lott.Elab.Basic
import Lott.Parser.OrJudgement

namespace Lott

open Lean

@[macro Lott.judgementEmbed]
private
def orJudgementImpl : Macro := fun stx => do
  let `([[$j₀:Lott.Judgement ∨ $j₁:Lott.Judgement]]) := stx | Macro.throwUnsupported
  ``([[$j₀:Lott.Judgement]] ∨ [[$j₁:Lott.Judgement]])

end Lott
