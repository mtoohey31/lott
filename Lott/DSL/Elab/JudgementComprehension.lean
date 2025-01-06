import Lott.DSL.Elab.Basic
import Lott.DSL.Parser.JudgementComprehension

namespace Lott.DSL.Elab

open Lean.Elab

@[lott_term_elab Lott.DSL.judgementComprehension]
private
def judgementComprehensionTermElab : TermElab := fun _ stx => do
  let `(Lott.Judgement| </ $«judgement»:Lott.Judgement // $p:term in $c:term />) := stx
    | throwUnsupportedSyntax
  let ft ← `(∀ x ∈ $c, let $p:term := x; [[$«judgement»:Lott.Judgement]])
  Lean.Elab.Term.elabTerm ft none

end Lott.DSL.Elab
