import Lott
import Lott.DSL.Elab.UniversalJudgement

namespace LottExamples.Lambda

locally_nameless
metavar Var, x

nonterminal Term, M, N :=
  | x             : var
  | "λ " x ". " M : lam (bind x in M)
  | M N           : app
  | "(" M ")"     : paren (desugar := return M)

-- Alpha reduction is not included since locally nameless representation makes it meaningless.

judgement_syntax M " ->ᵦ " N : BetaReduction

judgement BetaReduction :=

─────────────────── mk
(λ x. M) N ->ᵦ M^^N

judgement_syntax "lc" "(" M ")" : Term.VarLocallyClosed₀

abbrev Term.VarLocallyClosed₀ M := Term.VarLocallyClosed M

judgement_syntax M " ->η " N : EtaReduction

judgement EtaReduction :=

lc(M)
────────────── mk
λ x. M x$0 ->η M

end LottExamples.Lambda
