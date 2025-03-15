import Lott

namespace LottExamples.Lambda

locally_nameless
metavar Var, x

nonterminal Term, e :=
  | x             : var
  | "λ " x ". " e : lam (bind x in e)
  | e₀ e₁         : app
  | "(" e ")"     : paren notex (expand := return e)

end LottExamples.Lambda
