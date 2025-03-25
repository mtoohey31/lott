import Lott.Parser.NoTexJudgement

namespace Lott

open Lean

@[macro Lott.judgementEmbed]
private
def noTexJudgementImpl : Macro := fun stx => do
  let `([[notex $j:Lott.Judgement]]) := stx | Macro.throwUnsupported
  ``([[$j:Lott.Judgement]])

end Lott
