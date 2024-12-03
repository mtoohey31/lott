import Lott

namespace LottExamples.Lambda

locally_nameless
metavar Var, x

nonterminal Term, e :=
  | x             : var
  | "λ " x ". " e : lam (bind x in e)
  | e₀ e₁         : app
  | "(" e ")"     : paren (desugar := return e)

-- Alpha reduction is not included since locally nameless representation makes it meaningless.

judgement_syntax e " ->ᵦ " e' : BetaReduction

judgement BetaReduction :=

─────────────────────── mk
(λ x. e₀) e₁ ->ᵦ e₀^^e₁

judgement_syntax "lc" "(" e ")" : Term.VarLocallyClosed₀

abbrev Term.VarLocallyClosed₀ e := Term.VarLocallyClosed e

judgement_syntax e " ->η " e' : EtaReduction

judgement EtaReduction :=

lc(e)
──────────────── mk
λ x. e x$0 ->η e

end LottExamples.Lambda
