import LottExamples.Lambda.Syntax

namespace LottExamples.Lambda

-- Alpha reduction is not included since locally nameless representation makes it meaningless.

judgement_syntax e " ->ᵦ " e' : BetaReduction (tex := s!"{e} \\, \\lottsym\{\\stackrel\{β}\{→}} \\, {e'}")

judgement BetaReduction where

───────────────────────── mk
(λ x. e₀) e₁ ->ᵦ e₀^^e₁/x

judgement_syntax "lc" "(" e ")" : Term.VarLocallyClosed

judgement_syntax e " ->η " e' : EtaReduction (tex := s!"{e} \\, \\lottsym\{\\stackrel\{η}\{→}} \\, {e'}")

judgement EtaReduction where

lc(e)
──────────────── mk
λ x. e x$0 ->η e

end LottExamples.Lambda
