import Lott

namespace LottExamples.STLC

set_option lott.tex.example.singleProductionInline false

nonterminal «Type», τ :=
  | τ₀ " → " τ₁ : arr

locally_nameless
metavar Var, x

nonterminal Term, e :=
  | x             : var
  | "λ " x ". " e : lam (bind x in e)
  | e₀ e₁         : app
  | "(" e ")"     : paren notex (expand := return e)

nonterminal Environment, Γ :=
  | "ε"              : empty
  | Γ ", " x " : " τ : ext (id x)
  | Γ₀ ", " Γ₁       : append notex (expand := return .mkCApp `LottExamples.STLC.Environment.append #[Γ₀, Γ₁])

nonterminal (parent := Term) Value, v :=
  | "λ " x ". " e : lam (bind x in e)

end LottExamples.STLC
