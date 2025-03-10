import Lott.Elab.Basic
import Lott.Parser.UniversalJudgement

namespace Lott.Elab

open Lean.Elab
open Lean.Parser.Term

@[lott_term_elab Lott.universalJudgement]
private
def universalJudgementTermElab : TermElab := fun _ stx => do
  let `(Lott.Judgement| ∀ $[$binders]* $[$type?]?, $«judgement»:Lott.Judgement) := stx
    | throwUnsupportedSyntax
  let stx' ← ``(∀ $binders* $[$type?:typeSpec]?, [[$«judgement»:Lott.Judgement]])
  Lean.Elab.Term.elabTerm stx' none

@[lott_term_elab Lott.universalPredJudgement]
private
def universalPredJudgementTermElab : TermElab := fun _ stx => do
  let stx' ← match stx with
  | `(Lott.Judgement| ∀ $i:ident $bp:binderPred, $«judgement»:Lott.Judgement) =>
    ``(∀ $i:ident, satisfies_binder_pred% $i $bp → [[$«judgement»:Lott.Judgement]])
  | `(Lott.Judgement| ∀ $i:ident, $«judgement»:Lott.Judgement) =>
    ``(∀ $i:ident, [[$«judgement»:Lott.Judgement]])
  | _ => throwUnsupportedSyntax
  Lean.Elab.Term.elabTerm stx' none

end Lott.Elab
