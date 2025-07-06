import Lott.Elab.Basic
import Lott.Parser.NotJudgement

namespace Lott

open Lean
open Lean.Elab

@[macro Lott.judgementEmbed]
private
def notJudgementImpl : Macro := fun stx => do
  let `([[¬$j:Lott.Judgement]]) := stx | Macro.throwUnsupported
  ``(¬[[$j:Lott.Judgement]])

@[lott_tex_elab notJudgement]
private
def notJudgementTexElab : TexElab := fun profile ref stx => do
  let `(Lott.Judgement| ¬$j:Lott.Judgement) := stx | throwUnsupportedSyntax
  let jTex ← texElabSymbolOrJudgement j.raw.getKind profile ref j
  return s!"\\lottsym\{¬} \\, {jTex}"

end Lott
