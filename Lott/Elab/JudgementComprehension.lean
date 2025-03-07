import Lott.Elab.Basic
import Lott.Parser.JudgementComprehension

namespace Lott.Elab

open Lean.Elab

@[lott_term_elab Lott.judgementComprehension]
private
def judgementComprehensionTermElab : TermElab := fun _ stx => do
  let `(Lott.Judgement| </ $«judgement»:Lott.Judgement // $p:term in $c:term />) := stx
    | throwUnsupportedSyntax
  let ft ← `(∀ x ∈ $c, let $p:term := x; [[$«judgement»:Lott.Judgement]])
  Lean.Elab.Term.elabTerm ft none

end Lott.Elab
