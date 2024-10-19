import Lott.DSL.Elab.Basic
import Lott.DSL.Parser.JudgementComprehension

namespace Lott.DSL.Elab

open Lean.Elab

@[lott_term_elab Lott.DSL.judgementComprehension]
private
def judgementComprehensionTermElab : TermElab := fun _ stx => do
  let `(Lott.Judgement| </ $«judgement»:Lott.Judgement // $i ∈ $c />) := stx
    | throwUnsupportedSyntax
  Lean.Elab.Term.elabTerm (← ``(∀ $i:ident ∈ $c, [[$«judgement»:Lott.Judgement]])) none

end Lott.DSL.Elab
