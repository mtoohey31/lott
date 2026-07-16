import Lott
import Lott.Elab.Nat

namespace LottExamples.STLC

nonterminal «Type», τ :=
  | τ₀ " → " τ₁ : arr
  | "ℕ"         : nat

locally_nameless
metavar Var, x

nonterminal Term, e :=
  | x             : var
  | "λ " x ". " e : lam (bind x in e)
  | e₀ e₁         : app
  | n             : nat
  | "(" e ")"     : paren notex (expand := return e)

nonterminal Environment, Γ :=
  | "ε"              : empty
  | Γ ", " x " : " τ : ext (id x)
  | Γ₀ ", " Γ₁       : append notex (expand := return .mkCApp `LottExamples.STLC.Environment.append #[Γ₀, Γ₁])

nonterminal (parent := Term) Value, v :=
  | "λ " x ". " e : lam (bind x in e)
  | n             : nat

end LottExamples.STLC
