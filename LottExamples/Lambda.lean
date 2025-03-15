import Lott

namespace LottExamples.Lambda

locally_nameless
metavar Var, x

nonterminal Term, e :=
  | x             : var
  | "λ " x ". " e : lam (bind x in e)
  | e₀ e₁         : app
  | "(" e ")"     : paren notex (expand := return e)

-- Alpha reduction is not included since locally nameless representation makes it meaningless.

judgement_syntax e " ->ᵦ " e' : BetaReduction (tex := s!"{e} \\; \\lottsym\{\\stackrel\{β}\{→}} \\; {e'}")

judgement BetaReduction :=

───────────────────────── mk
(λ x. e₀) e₁ ->ᵦ e₀^^e₁/x

judgement_syntax "lc" "(" e ")" : Term.VarLocallyClosed

judgement_syntax e " ->η " e' : EtaReduction (tex := s!"{e} \\; \\lottsym\{\\stackrel\{η}\{→}} \\; {e'}")

judgement EtaReduction :=

lc(e)
──────────────── mk
λ x. e x$0 ->η e

#filter "Lambda/intro.tex.lotttmpl"

end LottExamples.Lambda
