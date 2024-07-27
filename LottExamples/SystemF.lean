import Lott

namespace LottExamples.SystemF

open Lean

metavar TypeVar, a
metavar TermVar, x, y

nonterminal Type', A, B :=
  | a                   : var
  | A " → " B           : arr
  | "∀ " a ". " A       : forall'
  | A "[" a " ↦ " B "]" : subst (elab := return mkAppN (.const `LottExamples.SystemF.Type'.subst []) #[A, a, B])

def Type'.subst (A : Type') (a : TypeVar) (B : Type') : Type' := match A with
  | .var a' => if a' == a then B else .var a'
  | .arr A' B' => .arr (A'.subst a B) (B'.subst a B)
  | .forall' a' A' => .forall' a' <| if a' == a then A else A'.subst a B

nonterminal Term, E, F :=
  | x                     : var
  | "λ " x " : " A ". " E : lam
  | E F                   : app
  | "Λ " a ". " E         : typeGen
  | E " [" A "]"          : typeApp
  | "(" E ")"             : paren (desugar := return E)
  | E "[" x " ↦ " F "]"   : subst (elab := return mkAppN (.const `LottExamples.SystemF.Term.tmSubst []) #[E, x, F])
  | E "[" a " ↦ " A "]"   : typeSubst (elab := return mkAppN (.const `LottExamples.SystemF.Term.tySubst []) #[E, a, A])

def Term.tmSubst (E : Term) (x : TermVar) (F : Term) : Term := match E with
  | .var x' => if x' == x then F else .var x'
  | .lam x' A E' => .lam x' A <| if x' == x then E' else E'.tmSubst x F
  | .app E' F' => .app (E'.tmSubst x F) (F'.tmSubst x F)
  | .typeGen a E' => .typeGen a <| E'.tmSubst x F
  | .typeApp E' A => .typeApp (E'.tmSubst x F) A

def Term.tySubst (E : Term) (a : TypeVar) (A : Type') : Term := match E with
  | .var x => .var x
  | .lam x A' E => .lam x (A'.subst a A) (E.tySubst a A)
  | .app E' F => .app (E'.tySubst a A) (F.tySubst a A)
  | .typeGen a' E' => .typeGen a' <| if a' == a then E' else E'.tySubst a A
  | .typeApp E' A' => .typeApp (E'.tySubst a A) (A'.subst a A)

nonterminal Environment, G :=
  | "ε"              : empty
  | G ", " x " : " A : termVarExt
  | G ", " a         : typeVarExt

judgement_syntax x " : " A " ∈ " G : TermVarInEnvironment

judgement TermVarInEnvironment :=

──────────────── head
x : A ∈ G, x : A

x : A ∈ G
──────────────── termVarExt
x : A ∈ G, y : B

x : A ∈ G
──────────── typeVarExt
x : A ∈ G, a

example : ¬[[x : A ∈ ε]] := by intro h; cases h

judgement_syntax G " |- " E " : " A : Typing

judgement Typing :=

x : A ∈ G
────────── Var
G |- x : A

G, x : A |- E : B
─────────────────────── Lam
G |- λ x : A. E : A → B

x : A ∈ G
G |- E : A → B
G |- F : A
────────────── App
G |- E F : B

G, a |- E : A
──────────────────── TypeGen
G |- Λ a. E : ∀ a. A

G |- E : ∀ a. A
────────────────────── TypeApp
G |- E [B] : A [a ↦ B]

-- TODO: Define operational semantics.

-- TODO: Prove preservation and progress.

end LottExamples.SystemF
