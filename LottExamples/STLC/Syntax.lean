import Lott
import Lott.Elab.Nat

namespace LottExamples.STLC

nonterminal «Type», τ :=
  | τ₀ " → " τ₁ : arr
  | "ℕ"         : nat

-- #print «Type»

-- #check [[ℕ → ℕ → ℕ]]

/- #eval do
  let stx ← `(Lott.Symbol| ℕ → ℕ)
  let s ← Lott.texElabSymbolOrJudgement (Lott.symbolPrefix ++ ``«Type») default default stx
  Lean.logInfo s -/

locally_nameless
metavar Var, x

-- #print Var

nonterminal Term, e :=
  | x             : var
  | "λ " x ". " e : lam (bind x in e)
  | e₀ e₁         : app
  | n             : nat
  | "(" e ")"     : paren notex (expand := return e)

-- #check Term.Var_subst
-- #check Term.VarLocallyClosed

nonterminal Environment, Γ :=
  | "ε"              : empty
  | Γ ", " x " : " τ : ext (id x)
  | Γ₀ ", " Γ₁       : append notex (expand := return .mkCApp `LottExamples.STLC.Environment.append #[Γ₀, Γ₁])
  | "(" Γ ")"        : paren notex (expand := return Γ)

nonterminal (parent := Term) Value, v :=
  | "λ " x ". " e : lam (bind x in e)
  | n             : nat

end LottExamples.STLC
