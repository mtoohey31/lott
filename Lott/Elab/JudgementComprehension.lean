import Lott.Elab.Basic
import Lott.Parser.JudgementComprehension

namespace Lott

open Lean

@[macro judgementEmbed]
private
def judgementComprehensionImpl : Macro := fun stx => do
  let `([[</ $«judgement»:Lott.Judgement // $p:term in $c:term />]]) := stx
    | Macro.throwUnsupported
  `(∀ x ∈ $c, let $p:term := x; [[$«judgement»:Lott.Judgement]])

end Lott
