import Lott.Elab.UniversalJudgement
import LottExamples.STLC.Syntax

namespace LottExamples.STLC

judgement_syntax x " ≠ " x' : VarId.Ne (id x, x')

judgement VarId.Ne := _root_.Ne (α := VarId)

namespace Environment

termonly def append (Γ₀ : Environment) : Environment → Environment
  | [[ε]] => Γ₀
  | [[Γ₁, x : τ]] => append Γ₀ Γ₁ |>.ext x τ

termonly def dom : Environment → List VarId
  | empty => []
  | ext Γ x _ => x :: dom Γ

-- Compromise: Defining judgement syntax and implementation must be two separate commands.

judgement_syntax LottExamples.STLC.x " : " LottExamples.STLC.τ " ∈ " Γ : Mem (id x)

judgement Mem where

──────────────── head
x : τ ∈ Γ, x : τ

x : τ ∈ Γ
x ≠ x'
────────────────── ext
x : τ ∈ Γ, x' : τ'

judgement_syntax LottExamples.STLC.x " ∈ " Γ : Mem' (id x)

termonly abbrev Mem' := fun x Γ => ∃ τ, [[x : τ ∈ Γ]]

judgement_syntax LottExamples.STLC.x " ∉ " Γ : NotMem (id x)

termonly abbrev NotMem := fun x Γ => ¬[[x ∈ Γ]]

judgement_syntax "⊢ " Γ : WellFormedness

judgement WellFormedness where

─── empty
⊢ ε

⊢ Γ
x ∉ Γ
────────── ext
⊢ Γ, x : τ

end Environment

namespace Term

judgement_syntax LottExamples.STLC.Γ " ⊢ " e " : " LottExamples.STLC.τ : Typing

judgement Typing where

notex ⊢ Γ
x : τ ∈ Γ
───────── var
Γ ⊢ x : τ

∀ x ∉ I, Γ, x : τ₀ ⊢ e^x : τ₁
───────────────────────────── lam (I : List VarId)
Γ ⊢ λ x. e : τ₀ → τ₁

Γ ⊢ e₀ : τ₀ → τ₁
Γ ⊢ e₁ : τ₀
──────────────── app
Γ ⊢ e₀ e₁ : τ₁

───────── nat
Γ ⊢ n : ℕ

judgement_syntax e " → " e' : Reduction (tex := s!"{e} \\, \\lottsym\{\\longrightarrow} \\, {e'}")

judgement Reduction where

e₀ → e₀'
────────────── appl
e₀ e₁ → e₀' e₁

e → e'
────────── appr
v e → v e'

─────────────────── lamApp
(λ x. e) v → e^^v/x

end Term

end LottExamples.STLC
