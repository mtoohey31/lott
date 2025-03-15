import Lott.Data.List
import Lott.Elab.UniversalJudgement
import LottExamples.SystemF.Syntax

namespace LottExamples.SystemF

namespace Environment

termonly
def append (Γ : Environment) : Environment → Environment
  | empty => Γ
  | termVarExt Γ' x A => Γ.append Γ' |>.termVarExt x A
  | typeVarExt Γ' a => Γ.append Γ' |>.typeVarExt a

termonly
def TypeVar_subst (Γ : Environment) (a : TypeVarId) (A : «Type») := match Γ with
  | [[ε]] => empty
  | [[Γ', x : A']] => Γ'.TypeVar_subst a A |>.termVarExt x <| A'.TypeVar_subst a A
  | [[Γ', a']] => Γ'.TypeVar_subst a A |>.typeVarExt a'

termonly
def termVar_count : Environment → Nat
  | [[ε]] => 0
  | [[Γ, x : A]] => 1 + Γ.termVar_count
  | [[Γ, a]] => Γ.termVar_count

termonly
def typeVar_count : Environment → Nat
  | [[ε]] => 0
  | [[Γ, x : A]] => Γ.typeVar_count
  | [[Γ, a]] => 1 + Γ.typeVar_count

termonly
def termVar_domain : Environment → List TermVarId
  | [[ε]] => []
  | [[Γ, x : A]] => x :: Γ.termVar_domain
  | [[Γ, a]] => Γ.termVar_domain

termonly
def typeVar_domain : Environment → List TypeVarId
  | [[ε]] => []
  | [[Γ, x : A]] => Γ.typeVar_domain
  | [[Γ, a]] => a :: Γ.typeVar_domain

end Environment

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

judgement TypeVarNe := Ne (α := TypeVarId)

judgement_syntax a " ∈ " Γ : TypeVarInEnvironment (id a)

judgement TypeVarInEnvironment where

──────── head
a ∈ Γ, a

a ∈ Γ
──────────── termVarExt
a ∈ Γ, x : A

a ∈ Γ
a ≠ a'
───────── typeVarExt
a ∈ Γ, a'

judgement_syntax a " ∉ " Γ : TypeVarNotInEnvironment (id a)

judgement TypeVarNotInEnvironment := fun a Γ => ¬[[a ∈ Γ]]

judgement_syntax x " ≠ " y : TermVarNe (id x, y)

judgement TermVarNe := Ne (α := TermVarId)

judgement_syntax x " : " A " ∈ " Γ : TermVarInEnvironment (id x)

judgement TermVarInEnvironment where

──────────────── head
x : A ∈ Γ, x : A

x : A ∈ Γ
x ≠ x'
───────────────── termVarExt
x : A ∈ Γ, x' : B

x : A ∈ Γ
──────────── typeVarExt
x : A ∈ Γ, a

judgement_syntax x " ∉ " Γ : TermVarNotInEnvironment (id x)

judgement TermVarNotInEnvironment := fun x Γ => ∀ A, ¬[[x : A ∈ Γ]]

judgement_syntax a " ∈ " "ftv" "(" A ")" : Type.InFreeTypeVars (id a)

judgement Type.InFreeTypeVars := fun a (A : «Type») => a ∈ A.freeTypeVars

judgement_syntax a " ∉ " "ftv" "(" A ")" : Type.NotInFreeTypeVars (id a)

judgement Type.NotInFreeTypeVars := fun a A => ¬[[a ∈ ftv(A)]]

judgement_syntax x " ∈ " "fv" "(" E ")" : Term.InFreeTermVars (id x)

judgement Term.InFreeTermVars := fun x (E : Term) => x ∈ E.freeTermVars

judgement_syntax x " ∉ " "fv" "(" E ")" : Term.NotInFreeTermVars (id x)

judgement Term.NotInFreeTermVars := fun x E => ¬[[x ∈ fv(E)]]

judgement_syntax a " ∈ " "ftv" "(" E ")" : Term.InFreeTypeVars (id a)

judgement Term.InFreeTypeVars := fun a (E : Term) => a ∈ E.freeTypeVars

judgement_syntax a " ∉ " "ftv" "(" E ")" : Term.NotInFreeTypeVars (id a)

judgement Term.NotInFreeTypeVars := fun a E => ¬[[a ∈ ftv(E)]]

judgement_syntax Γ " ⊢ " A : TypeWellFormedness

judgement TypeWellFormedness where

a ∈ Γ
───── var
Γ ⊢ a

Γ ⊢ A
Γ ⊢ B
───────── arr
Γ ⊢ A → B

∀ a ∉ I, Γ, a ⊢ A^a
────────────────────────────── forall' {I : List TypeVarId}
Γ ⊢ ∀ a. A

judgement_syntax x " ∈ " "dom" "(" Γ ")" : TermVarInEnvironmentDomain (id x)

judgement TermVarInEnvironmentDomain := fun x (Γ : Environment) => x ∈ Γ.termVar_domain

judgement_syntax x " ∉ " "dom" "(" Γ ")" : TermVarNotInEnvironmentDomain (id x)

judgement TermVarNotInEnvironmentDomain := fun x Γ => ¬[[x ∈ dom(Γ)]]

judgement_syntax a " ∈ " "dom" "(" Γ ")" : TypeVarInEnvironmentDomain (id a)

judgement TypeVarInEnvironmentDomain := fun a (Γ : Environment) => a ∈ Γ.typeVar_domain

judgement_syntax a " ∉ " "dom" "(" Γ ")" : TypeVarNotInEnvironmentDomain (id a)

judgement TypeVarNotInEnvironmentDomain := fun a Γ => ¬[[a ∈ dom(Γ)]]

judgement_syntax "⊢ " Γ : EnvironmentWellFormedness

judgement EnvironmentWellFormedness where

─── empty
⊢ ε

⊢ Γ
Γ ⊢ A
x ∉ dom(Γ)
────────── termVarExt
⊢ Γ, x : A

⊢ Γ
a ∉ dom(Γ)
────────── typeVarExt
⊢ Γ, a

judgement_syntax Γ " ⊢ " E " : " A : Typing

judgement Typing where

⊢ Γ
x : A ∈ Γ
───────── var
Γ ⊢ x : A

Γ ⊢ A
∀ x ∉ I, Γ, x : A ⊢ E^x : B
────────────────────────────────────── lam {I : List TermVarId}
Γ ⊢ λ x : A. E : A → B

Γ ⊢ E : A → B
Γ ⊢ F : A
───────────── app
Γ ⊢ E F : B

∀ a ∉ I, Γ, a ⊢ E^a : A^a
──────────────────────────────────── typeGen {I : List TypeVarId}
Γ ⊢ Λ a. E : ∀ a. A

Γ ⊢ E : ∀ a. A
Γ ⊢ B
────────────────── typeApp
Γ ⊢ E [B] : A^^B/a

judgement_syntax E " -> " F : OperationalSemantics (tex := s!"{E} \\, \\lottsym\{→} \\, {F}")

judgement OperationalSemantics where

E -> E'
─────────── appl
E F -> E' F

F -> F'
─────────── appr
V F -> V F'

──────────────────────── lamApp
(λ x : A. E) V -> E^^V/x

E -> E'
─────────────── typeApp
E [A] -> E' [A]

────────────────────── typeGenApp
(Λ a. E) [A] -> E^^A/a

end LottExamples.SystemF
