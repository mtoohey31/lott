import Lott.Parser.NoTexJudgement

namespace Lott

open Lean

@[macro Lott.judgementEmbed]
private
def noTexJudgementImpl : Macro := fun stx => do
  let `([[$j:Lott.Judgement notex]]) := stx | Macro.throwUnsupported
  ``([[$j:Lott.Judgement]])

end Lott
