import Lott

namespace LottExamples.STLC

nonterminal (tex pre := "\\mathcolor{STLC}{", post := "}") «Type», τ :=
  | τ₀ " → " τ₁ : arr
  | "Unit"      : unit

locally_nameless
metavar (tex pre := "\\mathcolor{STLC}{", post := "}") Var, x

nonterminal (tex pre := "\\mathcolor{STLC}{", post := "}") Term, e :=
  | x             : var
  | "λ " x ". " e : lam (bind x in e)
  | e₀ e₁         : app
  | "(" ")"       : unit
  | "(" e ")"     : paren notex (expand := return e)

nonterminal (tex pre := "\\mathcolor{STLC}{", post := "}") Environment, Γ :=
  | "ε"              : empty
  | Γ ", " x " : " τ : ext (id x)
  | Γ₀ ", " Γ₁       : append notex (expand := return .mkCApp `LottExamples.STLC.Environment.append #[Γ₀, Γ₁])

nonterminal (parent := Term) (tex pre := "\\mathcolor{STLC}{", post := "}") Value, v :=
  | "λ " x ". " e : lam (bind x in e)
  | "(" ")"       : unit

end LottExamples.STLC
