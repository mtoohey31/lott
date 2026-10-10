import Lott
import Lott.Elab.Nat

namespace LottExamples.STLC

nonterminal «Type», τ :=
  | τ₀ " → " τ₁ : arr
  | "ℕ"         : nat

-- #print «Type»
-- #check [[ℕ → ℕ → ℕ]]

-- #check Type.arr_parser
-- #check Type.arrImpl

-- #check Type.arrTexElab
-- #check Lott.TexElab

locally_nameless
metavar Var, x

-- #print Var
-- #eval return Lott.metaVarExt.getState (← Lean.getEnv)

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
