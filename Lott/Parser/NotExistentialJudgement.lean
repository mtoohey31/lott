module

public meta import Lott.Parser

namespace Lott

open Lean

syntax (name := notExistentialJudgement) "∄ " explicitBinders ", " withPosition(Lott.Judgement) : Lott.Judgement

end Lott
