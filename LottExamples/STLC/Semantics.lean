import Lott.Elab.UniversalJudgement
import LottExamples.STLC.Syntax

namespace LottExamples.STLC

judgement_syntax x " ≠ " x' : VarId.Ne (id x, x')

judgement VarId.Ne := fun (x x' : VarId) => x ≠ x'

judgement_syntax x " ∈ " "fv" "(" e ")" : Term.InFreeVars (id x)

judgement Term.InFreeVars := fun x (e : Term) => x ∈ e.freeVars

judgement_syntax x " ∉ " "fv" "(" e ")" : Term.NotInFreeVars (id x)

judgement Term.NotInFreeVars := fun x e => ¬[[x ∈ fv(e)]]

namespace Environment

termonly
def append (Γ₀ : Environment) : Environment → Environment
  | [[ε]] => Γ₀
  | [[Γ₁, x : τ]] => Γ₀.append Γ₁ |>.ext x τ

termonly
def empty_append (Γ : Environment) : Environment.empty.append Γ = Γ := match Γ with
  | [[ε]] => rfl
  | [[Γ', x : τ]] => by rw [append, Γ'.empty_append]

termonly
def append_assoc {Γ₀ : Environment} : Γ₀.append (Γ₁.append Γ₂) = (Γ₀.append Γ₁).append Γ₂ := by
  match Γ₂ with
  | [[ε]] => rfl
  | [[Γ₂', x : τ]] => rw [append, append, append_assoc, ← append]

termonly
def domain : Environment → List VarId
  | empty => []
  | ext Γ x _ => x :: Γ.domain

end Environment

judgement_syntax x " : " τ " ∈ " Γ : Environment.VarIn (id x)

judgement Environment.VarIn where

──────────────── head
x : τ ∈ Γ, x : τ

x : τ ∈ Γ
x ≠ x'
────────────────── ext
x : τ ∈ Γ, x' : τ'

judgement_syntax x " ∉ " Γ : Environment.VarNotIn (id x)

judgement Environment.VarNotIn := fun x Γ => ∀ τ, ¬[[x : τ ∈ Γ]]

judgement_syntax x " ∈ " "dom" "(" Γ ")" : Environment.VarInDom (id x)

judgement Environment.VarInDom := fun x (Γ : Environment) => x ∈ Γ.domain

judgement_syntax x " ∉ " "dom" "(" Γ ")" : Environment.VarNotInDom (id x)

judgement Environment.VarNotInDom := fun x Γ => ¬[[x ∈ dom(Γ)]]

judgement_syntax "⊢ " Γ : Environment.WellFormedness

judgement Environment.WellFormedness where

─── empty
⊢ ε

⊢ Γ
x ∉ dom(Γ)
────────── ext
⊢ Γ, x : τ

judgement_syntax Γ " ⊢ " e " : " τ : Typing

judgement Typing where

⊢ Γ
x : τ ∈ Γ
───────── var
Γ ⊢ x : τ

∀ x ∉ I, Γ, x : τ₀ ⊢ e^x : τ₁
───────────────────────────── lam {I : List VarId}
Γ ⊢ λ x. e : τ₀ → τ₁

Γ ⊢ e₀ : τ₀ → τ₁
Γ ⊢ e₁ : τ₀
──────────────── app
Γ ⊢ e₀ e₁ : τ₁

───────────── unit
Γ ⊢ () : Unit

judgement_syntax e " ↦ " e' : Reduction

judgement Reduction where

e₀ ↦ e₀'
────────────── appl
e₀ e₁ ↦ e₀' e₁

e ↦ e'
────────── appr
v e ↦ v e'

─────────────────── lamApp
(λ x. e) v ↦ e^^v/x

end LottExamples.STLC
