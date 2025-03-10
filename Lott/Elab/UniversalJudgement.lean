import Lott.Elab.Basic
import Lott.Parser.UniversalJudgement

namespace Lott

open Lean

@[macro judgementEmbed]
private
def universalJudgementImpl : Macro := fun stx => do
  let `([[∀ $[$binders]* $[$type?]?, $«judgement»:Lott.Judgement]]) := stx | Macro.throwUnsupported
  ``(∀ $binders* $[$type?:typeSpec]?, [[$«judgement»:Lott.Judgement]])

@[macro judgementEmbed]
private
def universalPredJudgementImpl : Macro
  | `([[∀ $i:ident $bp:binderPred, $«judgement»:Lott.Judgement]]) =>
    ``(∀ $i:ident, satisfies_binder_pred% $i $bp → [[$«judgement»:Lott.Judgement]])
  | `([[∀ $i:ident, $«judgement»:Lott.Judgement]]) =>
    ``(∀ $i:ident, [[$«judgement»:Lott.Judgement]])
  | _ => Macro.throwUnsupported

end Lott
