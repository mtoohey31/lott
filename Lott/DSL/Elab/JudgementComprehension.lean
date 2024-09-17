import Lott.Data.FinRange
import Lott.DSL.Elab.Basic

namespace Lott.DSL.Elab

open Lean.Elab

@[lott_term_elab Lott.DSL.judgementComprehension]
private
def judgementComprehensionTermElab : TermElab := fun stx => do
  let `(Lott.Judgement| </ $«judgement»:Lott.Judgement // $i ∈ [$start : $stop]ᶠ />) := stx |
    throwUnsupportedSyntax
  -- TODO: Figure out why Lean can't resolve the Membership instance here without help, then allow
  -- for arbitrary sets.
  Lean.Elab.Term.elabTerm (← `(∀ $i:ident, Membership.mem (self := Lott.Data.instMembershipFinFinRange) $i [$start : $stop]ᶠ → [[$«judgement»:Lott.Judgement]])) none

end Lott.DSL.Elab
