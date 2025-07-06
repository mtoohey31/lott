import Lott.Elab.Basic
import Lott.Parser.ImpliesJudgement

namespace Lott

open Lean
open Lean.Elab

@[macro Lott.judgementEmbed]
private
def impliesJudgementImpl : Macro := fun stx => do
  let `([[$j₀:Lott.Judgement ⇒ $j₁:Lott.Judgement]]) := stx | Macro.throwUnsupported
  ``([[$j₀:Lott.Judgement]] → [[$j₁:Lott.Judgement]])

@[lott_tex_elab impliesJudgement]
private
def impliesJudgementTexElab : TexElab := fun profile ref stx => do
  let `(Lott.Judgement| $j₀:Lott.Judgement ⇒ $j₁:Lott.Judgement) := stx | throwUnsupportedSyntax
  let j₀Tex ← texElabSymbolOrJudgement j₀.raw.getKind profile ref j₀
  let j₁Tex ← texElabSymbolOrJudgement j₁.raw.getKind profile ref j₁
  return s!"{j₀Tex} \\, \\lottsym\{⇒} \\, {j₁Tex}"

end Lott
