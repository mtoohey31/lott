import Lott

namespace LottExamples.SystemF

locally_nameless
metavar TypeVar, a

nonterminal «Type», A, B :=
  | a                    : var
  | A " → " B            : arr
  | "∀ " a ". " A        : forall' (bind a in A)
  | "(" A ")"            : paren notex (expand := return A)

locally_nameless
metavar TermVar, x, y

nonterminal Term, E, F :=
  | x                     : var
  | "λ " x " : " A ". " E : lam (bind x in E)
  | E F                   : app
  | "Λ " a ". " E         : typeGen (bind a in E)
  | E " [" A "]"          : typeApp
  | "(" E ")"             : paren notex (expand := return E)

nosubst
nonterminal Environment, Γ :=
  | "ε"                  : empty
  | Γ ", " x " : " A     : termVarExt (id x)
  | Γ ", " a             : typeVarExt (id a)
  | Γ₀ ", " Γ₁             : append notex (expand := return .mkCApp `LottExamples.SystemF.Environment.append #[Γ₀, Γ₁])
  | "(" Γ ")"            : paren notex (expand := return Γ)
  | Γ " [" A " / " a "]" : subst notex (id a) (expand := return .mkCApp `LottExamples.SystemF.Environment.TypeVar_subst #[Γ, a, A])

nonterminal (parent := Term) Value, V :=
  | "λ " x " : " A ". " E : lam (bind x in E)
  | "Λ " a ". " E         : typeGen (bind a in E)

end LottExamples.SystemF
