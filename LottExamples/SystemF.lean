import Lott
import Lott.Data.List
import Lott.DSL.Elab.UniversalJudgement

namespace LottExamples.SystemF

open Lean

locally_nameless
metavar TypeVar, a, b

locally_nameless
metavar TermVar, x, y

nonterminal Type', A, B :=
  | a                    : var
  | A " → " B            : arr
  | "∀ " a ". " A        : forall' (bind a in A)
  | "(" A ")"            : paren (desugar := return A)

@[simp]
theorem Type'.TypeVar_open_sizeOf (A : Type') : sizeOf (A.TypeVar_open a n) = sizeOf A := by
  match A with
  | var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h' =>
      dsimp only [sizeOf]
      rw [← h', _sizeOf_1, _sizeOf_1]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse => rfl
  | var (.free _) =>
    rw [TypeVar_open]
    split
    · case isTrue => rw [if_neg id]
    · case isFalse => rfl
  | arr A' B =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Type', a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this (A'.TypeVar_open _ _), this (B.TypeVar_open _ _), this A', this B]
    rw [A'.TypeVar_open_sizeOf, B.TypeVar_open_sizeOf]
  | forall' A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Type', a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this (A'.TypeVar_open _ _), this A', A'.TypeVar_open_sizeOf]

theorem Type'.TypeVar_open_comm (A : Type') (anea' : a ≠ a') (mnen : m ≠ n)
  : (A.TypeVar_open a m).TypeVar_open a' n =
    (A.TypeVar_open a' n).TypeVar_open a m := by match A with
  | var (.free _) =>
    rw [TypeVar_open, if_neg (nomatch ·), TypeVar_open, if_neg (nomatch ·), TypeVar_open,
        if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      rw [← h, TypeVar_open, if_neg (nomatch ·), TypeVar_open,
          if_neg (mnen <| TypeVar.bound.inj ·.symm), TypeVar_open, if_pos rfl]
    · case isFalse h =>
      rw [TypeVar_open]
      split
      · case isTrue h' => rw [TypeVar_open, if_neg (nomatch ·)]
      · case isFalse h' => rw [TypeVar_open, if_neg h]
  | arr A' B =>
    rw [TypeVar_open, TypeVar_open, A'.TypeVar_open_comm anea' mnen, B.TypeVar_open_comm anea' mnen,
        ← TypeVar_open, ← TypeVar_open]
  | forall' A' =>
    rw [TypeVar_open, TypeVar_open]
    simp only
    rw [A'.TypeVar_open_comm anea' (mnen <| Nat.succ_inj'.mp ·), ← TypeVar_open, ← TypeVar_open]

inductive Type'.TypeVarLocallyClosed : Type' → Nat → Prop where
  | var_free : TypeVarLocallyClosed (.var (.free _)) n
  | var_bound : m < n → TypeVarLocallyClosed (.var (.bound m)) n
  | arr {A B : Type'}
    : A.TypeVarLocallyClosed n → B.TypeVarLocallyClosed n → (A.arr B).TypeVarLocallyClosed n
  | forall' {A : Type'} : A.TypeVarLocallyClosed (n + 1) → A.forall'.TypeVarLocallyClosed n

theorem Type'.TypeVarLocallyClosed.weaken {A : Type'}
  : A.TypeVarLocallyClosed m → A.TypeVarLocallyClosed (m + n)
  | var_free => var_free
  | var_bound h => var_bound <| Nat.lt_add_right _ h
  | arr A'lc Blc => arr A'lc.weaken Blc.weaken
  | forall' A'lc => by
    apply forall'
    rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc]
    exact A'lc.weaken

theorem Type'.TypeVarLocallyClosed.TypeVar_open_drop {A : Type'} (h : m < n)
  : (A.TypeVar_open a m).TypeVarLocallyClosed n → A.TypeVarLocallyClosed n := fun Alc => by
  match A with
  | .var _ =>
    rw [TypeVar_open] at Alc
    split at Alc
    · case isTrue h' =>
      rw [← h']
      exact var_bound h
    · case isFalse h' => exact Alc
  | .arr A' B =>
    rw [TypeVar_open] at Alc
    let .arr A'lc Blc := Alc
    exact arr (A'lc.TypeVar_open_drop h) (Blc.TypeVar_open_drop h)
  | .forall' A' =>
    rw [TypeVar_open] at Alc
    let .forall' A'lc := Alc
    exact forall' <| A'lc.TypeVar_open_drop <| Nat.add_lt_add_iff_right.mpr h

theorem Type'.TypeVarLocallyClosed.TypeVar_open_eq {A : Type'} (h : A.TypeVarLocallyClosed m)
  (mlen : m ≤ n) : A.TypeVar_open x n = A := by match A, h with
  | var (.free _), var_free => rw [TypeVar_open, if_neg (nomatch ·)]
  | var (.bound _), var_bound lt =>
    have := Nat.ne_of_lt <| Nat.lt_of_lt_of_le lt mlen
    rw [TypeVar_open, if_neg fun x => this.symm <| TypeVar.bound.inj x]
  | .arr A' B, arr A'lc Blc =>
    rw [TypeVar_open, A'lc.TypeVar_open_eq mlen, Blc.TypeVar_open_eq mlen]
  | .forall' A, forall' A'lc =>
    rw [TypeVar_open]
    simp only
    rw [A'lc.TypeVar_open_eq (Nat.add_le_add_iff_right.mpr mlen)]

theorem Type'.TypeVarLocallyClosed.Type'_open_eq {A : Type'} (h : A.TypeVarLocallyClosed m)
  (mlen : m ≤ n) : A.Type'_open B n = A := by match A, h with
  | var (.free _), var_free => rw [Type'_open, if_neg (nomatch ·)]
  | var (.bound _), var_bound lt =>
    have := Nat.ne_of_lt <| Nat.lt_of_lt_of_le lt mlen
    rw [Type'_open, if_neg fun x => this.symm <| TypeVar.bound.inj x]
  | .arr A' B, arr A'lc Blc =>
    rw [Type'_open, A'lc.Type'_open_eq mlen, Blc.Type'_open_eq mlen]
  | .forall' A, forall' A'lc =>
    rw [Type'_open]
    simp only
    rw [A'lc.Type'_open_eq (Nat.add_le_add_iff_right.mpr mlen)]

theorem Type'.Type'_open_comm (A : Type') {B A': Type'} (mnen : m ≠ n)
  (Blc : B.TypeVarLocallyClosed n) (A'lc : A'.TypeVarLocallyClosed m)
  : (A.Type'_open B m).Type'_open A' n =
    (A.Type'_open A' n).Type'_open B m := by match A with
  | var (.free _) =>
    rw [Type'_open, if_neg (nomatch ·), Type'_open, if_neg (nomatch ·), Type'_open,
        if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [Type'_open]
    split
    · case isTrue h =>
      rw [← h, Blc.Type'_open_eq (Nat.le_refl _), Type'_open,
          if_neg (mnen <| TypeVar.bound.inj ·.symm), Type'_open, if_pos rfl]
    · case isFalse h =>
      rw [Type'_open]
      split
      · case isTrue h' => rw [A'lc.Type'_open_eq (Nat.le_refl _)]
      · case isFalse h' => rw [Type'_open, if_neg h]
  | arr A' B =>
    rw [Type'_open, Type'_open, A'.Type'_open_comm mnen Blc A'lc, B.Type'_open_comm mnen Blc A'lc,
        ← Type'_open, ← Type'_open]
  | forall' A' =>
    rw [Type'_open, Type'_open]
    simp only
    rw [A'.Type'_open_comm (mnen <| Nat.succ_inj'.mp ·) (Blc.weaken (n := 1))
          (A'lc.weaken (n := 1)), ← Type'_open, ← Type'_open]

theorem Type'.TypeVar_open_Type'_open_eq {A B : Type'} (Blc : B.TypeVarLocallyClosed m)
  (mnen : m ≠ n) : (A.TypeVar_open a m).Type'_open B n = (A.Type'_open B n).TypeVar_open a m := by
  match A with
  | var (.free _) =>
    rw [TypeVar_open, if_neg (nomatch ·), Type'_open, if_neg (nomatch ·), TypeVar_open,
        if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      rw [Type'_open, if_neg (nomatch ·), Type'_open, ← h,
          if_neg (mnen <| TypeVar.bound.inj ·.symm), TypeVar_open, if_pos rfl]
    · case isFalse h =>
      rw [Type'_open]
      split
      · case isTrue h' => rw [Blc.TypeVar_open_eq (Nat.le_refl _)]
      · case isFalse h' => rw [TypeVar_open, if_neg h]
  | arr A' B' =>
    rw [TypeVar_open, Type'_open, TypeVar_open_Type'_open_eq Blc mnen,
        TypeVar_open_Type'_open_eq Blc mnen, ← TypeVar_open, ← Type'_open]
  | forall' A' =>
    rw [TypeVar_open, Type'_open]
    simp only
    rw [TypeVar_open_Type'_open_eq Blc.weaken
          (by exact mnen <| Nat.succ_inj'.mp ·), ← TypeVar_open, ← Type'_open]

theorem Type'.TypeVar_open_Type'_open_eq' {A B : Type'} (Blc : B.TypeVarLocallyClosed n)
  : (A.TypeVar_open a n).Type'_open B n = A.TypeVar_open a n := by
  match A with
  | var (.free _) =>
    rw [TypeVar_open, if_neg (nomatch ·), Type'_open, if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h => rw [Type'_open, if_neg (nomatch ·)]
    · case isFalse h => rw [Type'_open, if_neg h]
  | arr A' B' =>
    rw [TypeVar_open, Type'_open, TypeVar_open_Type'_open_eq' Blc, TypeVar_open_Type'_open_eq' Blc,
        ← TypeVar_open]
  | forall' A' =>
    rw [TypeVar_open, Type'_open]
    simp only
    rw [TypeVar_open_Type'_open_eq' Blc.weaken, ← TypeVar_open]

theorem Type'.TypeVar_subst_TypeVar_open_comm {A B : Type'} (Blc : B.TypeVarLocallyClosed n)
  (anea' : a ≠ a')
  : (A.TypeVar_subst a B).TypeVar_open a' n = (A.TypeVar_open a' n).TypeVar_subst a B := by
  match A with
  | var (.free _) =>
    rw [TypeVar_subst]
    split
    · case isTrue h =>
      rw [TypeVar_open, if_neg (nomatch ·), TypeVar_subst, if_pos h,
          Blc.TypeVar_open_eq <| Nat.le_refl _]
    · case isFalse h => rw [TypeVar_open, if_neg (nomatch ·), TypeVar_subst, if_neg h]
  | var (.bound _) =>
    rw [TypeVar_subst, if_neg (nomatch ·), TypeVar_open]
    split
    · case isTrue h =>
      rw [TypeVar_subst, if_neg fun freeaeqfreea' => anea' <| TypeVar.free.inj freeaeqfreea']
    · case isFalse h => rw [TypeVar_subst, if_neg (nomatch ·)]
  | arr A' B' =>
    rw [TypeVar_subst, TypeVar_open, TypeVar_subst_TypeVar_open_comm Blc anea',
        TypeVar_subst_TypeVar_open_comm Blc anea', ← TypeVar_subst, ← TypeVar_open]
  | forall' A' =>
    rw [TypeVar_subst, TypeVar_open]
    simp only
    rw [TypeVar_subst_TypeVar_open_comm Blc.weaken anea', ← TypeVar_subst, ← TypeVar_open]

nonterminal Term, E, F :=
  | x                     : var
  | "λ " x " : " A ". " E : lam (bind x in E)
  | E F                   : app
  | "Λ " a ". " E         : typeGen (bind a in E)
  | E " [" A "]"          : typeApp
  | "(" E ")"             : paren (desugar := return E)

@[simp]
theorem Term.TermVar_open_sizeOf (E : Term) : sizeOf (E.TermVar_open x n) = sizeOf E := by
  match E with
  | var (.bound _) =>
    rw [TermVar_open]
    split
    · case isTrue h' =>
      dsimp only [sizeOf]
      rw [← h', _sizeOf_1, _sizeOf_1]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse => rfl
  | var (.free _) =>
    rw [TermVar_open]
    split
    · case isTrue => rw [if_neg id]
    · case isFalse => rfl
  | lam A E' =>
    dsimp [sizeOf]
    rw [TermVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Term, a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, this _]
    have : ∀ a : Type', a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, E'.TermVar_open_sizeOf]
  | app E' F =>
    dsimp [sizeOf]
    rw [TermVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Term, a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, this _, this _, this _, E'.TermVar_open_sizeOf,
        F.TermVar_open_sizeOf]
  | typeGen E' =>
    dsimp [sizeOf]
    rw [TermVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Term, a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, this _, E'.TermVar_open_sizeOf]
  | typeApp E' A =>
    dsimp [sizeOf]
    rw [TermVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Term, a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, this _]
    have : ∀ a : Type', a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, E'.TermVar_open_sizeOf]

@[simp]
theorem Term.TypeVar_open_sizeOf (E : Term) : sizeOf (E.TypeVar_open x n) = sizeOf E := by
  match E with
  | var _ => rw [TypeVar_open]
  | lam A E' =>
    dsimp [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Term, a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, this _]
    have : ∀ a : Type', a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, A.TypeVar_open_sizeOf, E'.TypeVar_open_sizeOf]
  | app E' F =>
    dsimp [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Term, a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, this _, this _, this _, E'.TypeVar_open_sizeOf, F.TypeVar_open_sizeOf]
  | typeGen E' =>
    dsimp [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Term, a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, this _, E'.TypeVar_open_sizeOf]
  | typeApp E' A =>
    dsimp [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1]
    have : ∀ a : Term, a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, this _]
    have : ∀ a : Type', a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]
    rw [this _, E'.TypeVar_open_sizeOf, A.TypeVar_open_sizeOf]

theorem Term.TermVar_open_comm (E : Term) (xnex' : x ≠ x') (mnen : m ≠ n)
  : (E.TermVar_open x m).TermVar_open x' n =
    (E.TermVar_open x' n).TermVar_open x m := by match E with
  | var (.free _) =>
    rw [TermVar_open, if_neg (nomatch ·), TermVar_open, if_neg (nomatch ·), TermVar_open,
        if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [TermVar_open]
    split
    · case isTrue h =>
      rw [← h, TermVar_open, if_neg (nomatch ·), TermVar_open,
          if_neg (mnen <| TermVar.bound.inj ·.symm), TermVar_open, if_pos rfl]
    · case isFalse h =>
      rw [TermVar_open]
      split
      · case isTrue h' => rw [TermVar_open, if_neg (nomatch ·)]
      · case isFalse h' => rw [TermVar_open, if_neg h]
  | lam A E' =>
    rw [TermVar_open, TermVar_open]
    simp only
    rw [E'.TermVar_open_comm xnex' (mnen <| Nat.succ_inj'.mp ·), ← TermVar_open, ← TermVar_open]
  | app E' F =>
    rw [TermVar_open, TermVar_open, E'.TermVar_open_comm xnex' mnen, F.TermVar_open_comm xnex' mnen,
        ← TermVar_open, ← TermVar_open]
  | typeGen E' =>
    rw [TermVar_open, TermVar_open, E'.TermVar_open_comm xnex' mnen, ← TermVar_open, ← TermVar_open]
  | typeApp E' A =>
    rw [TermVar_open, TermVar_open, E'.TermVar_open_comm xnex' mnen, ← TermVar_open, ← TermVar_open]

theorem Term.TypeVar_open_comm (E : Term) (anea' : a ≠ a') (mnen : m ≠ n)
  : (E.TypeVar_open a m).TypeVar_open a' n =
    (E.TypeVar_open a' n).TypeVar_open a m := by match E with
  | var _ => rw [TypeVar_open, TypeVar_open, TypeVar_open]
  | lam A E' =>
    rw [TypeVar_open, TypeVar_open, A.TypeVar_open_comm anea' mnen, E'.TypeVar_open_comm anea' mnen,
        ← TypeVar_open, ← TypeVar_open]
  | app E' F =>
    rw [TypeVar_open, TypeVar_open, E'.TypeVar_open_comm anea' mnen, F.TypeVar_open_comm anea' mnen,
        ← TypeVar_open, ← TypeVar_open]
  | typeGen E' =>
    rw [TypeVar_open, TypeVar_open]
    simp only
    rw [E'.TypeVar_open_comm anea' (mnen <| Nat.succ_inj'.mp ·), ← TypeVar_open, ← TypeVar_open]
  | typeApp E' A =>
    rw [TypeVar_open, TypeVar_open, E'.TypeVar_open_comm anea' mnen, A.TypeVar_open_comm anea' mnen,
        ← TypeVar_open, ← TypeVar_open]

theorem Term.TermVar_open_Type'_open_comm (E : Term)
  : (E.TermVar_open x m).Type'_open A n = (E.Type'_open A n).TermVar_open x m := by match E with
  | var _ =>
    rw [TermVar_open]
    split
    · case isTrue h => rw [Type'_open, Type'_open, TermVar_open, if_pos h]
    · case isFalse h => rw [Type'_open, TermVar_open, if_neg h]
  | lam A' E' =>
     rw [TermVar_open, Type'_open, E'.TermVar_open_Type'_open_comm, ← TermVar_open, ← Type'_open]
  | app E' F =>
    rw [TermVar_open, Type'_open, E'.TermVar_open_Type'_open_comm, F.TermVar_open_Type'_open_comm,
        ← TermVar_open, ← Type'_open]
  | typeGen E' =>
    rw [TermVar_open, Type'_open]
    simp only
    rw [E'.TermVar_open_Type'_open_comm, ← TermVar_open, ← Type'_open]
  | typeApp E' A' =>
    rw [TermVar_open, Type'_open, E'.TermVar_open_Type'_open_comm, ← TermVar_open, ← Type'_open]

inductive Term.TermVarLocallyClosed : Term → Nat → Prop where
  | var_free : TermVarLocallyClosed (var (.free _)) n
  | var_bound : m < n → TermVarLocallyClosed (var (.bound m)) n
  | lam : E.TermVarLocallyClosed (n + 1) → (lam A E).TermVarLocallyClosed n
  | app {E F : Term}
    : E.TermVarLocallyClosed n → F.TermVarLocallyClosed n → (E.app F).TermVarLocallyClosed n
  | typeGen {E : Term} : E.TermVarLocallyClosed n → E.typeGen.TermVarLocallyClosed n
  | typeApp {E : Term} : E.TermVarLocallyClosed n → (E.typeApp A).TermVarLocallyClosed n

theorem Term.TermVarLocallyClosed.weaken {E : Term}
  : E.TermVarLocallyClosed m → E.TermVarLocallyClosed (m + n)
  | var_free => var_free
  | var_bound h => var_bound <| Nat.lt_add_right _ h
  | lam E'lc => by
    apply lam
    rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc]
    exact E'lc.weaken
  | app E'lc Flc => app E'lc.weaken Flc.weaken
  | typeGen E'lc => typeGen E'lc.weaken
  | typeApp E'lc => typeApp E'lc.weaken

theorem Term.TermVarLocallyClosed.TermVar_open_drop {E : Term} (h : m < n)
  : (E.TermVar_open x m).TermVarLocallyClosed n → E.TermVarLocallyClosed n := fun Elc => by
  match E with
  | .var _ =>
    rw [TermVar_open] at Elc
    split at Elc
    · case isTrue h' =>
      rw [← h']
      exact var_bound h
    · case isFalse h' => exact Elc
  | .lam _ E' =>
    rw [TermVar_open] at Elc
    let .lam E'lc := Elc
    exact lam <| E'lc.TermVar_open_drop <| Nat.add_lt_add_iff_right.mpr h
  | .app E' F =>
    rw [TermVar_open] at Elc
    let .app E'lc Flc := Elc
    exact app (E'lc.TermVar_open_drop h) (Flc.TermVar_open_drop h)
  | .typeGen E' =>
    rw [TermVar_open] at Elc
    let .typeGen E'lc := Elc
    exact typeGen <| E'lc.TermVar_open_drop h
  | .typeApp E' A =>
    rw [TermVar_open] at Elc
    let .typeApp E'lc := Elc
    exact typeApp <| E'lc.TermVar_open_drop h

theorem Term.TermVarLocallyClosed.TypeVar_open_drop {E : Term}
  : (E.TypeVar_open a m).TermVarLocallyClosed n → E.TermVarLocallyClosed n := fun Elc => by
  match E with
  | .var _ =>
    rw [TypeVar_open] at Elc
    exact Elc
  | .lam _ E' =>
    rw [TypeVar_open] at Elc
    let .lam E'lc := Elc
    exact lam E'lc.TypeVar_open_drop
  | .app E' F =>
    rw [TypeVar_open] at Elc
    let .app E'lc Flc := Elc
    exact app E'lc.TypeVar_open_drop Flc.TypeVar_open_drop
  | .typeGen E' =>
    rw [TypeVar_open] at Elc
    let .typeGen E'lc := Elc
    exact typeGen E'lc.TypeVar_open_drop
  | .typeApp E' A =>
    rw [TypeVar_open] at Elc
    let .typeApp E'lc := Elc
    exact typeApp E'lc.TypeVar_open_drop

theorem Term.TermVarLocallyClosed.TermVar_open_eq {E : Term} (h : E.TermVarLocallyClosed m)
  (mlen : m ≤ n) : E.TermVar_open x n = E := by match E, h with
  | var (.free _), var_free => rw [TermVar_open, if_neg (nomatch ·)]
  | var (.bound _), var_bound lt =>
    have := Nat.ne_of_lt <| Nat.lt_of_lt_of_le lt mlen
    rw [TermVar_open, if_neg fun x => this.symm <| TermVar.bound.inj x]
  | .lam A E', lam E'lc =>
    rw [TermVar_open]
    simp only
    rw [E'lc.TermVar_open_eq (Nat.add_le_add_iff_right.mpr mlen)]
  | .app E' F, app E'lc Flc =>
    rw [TermVar_open, E'lc.TermVar_open_eq mlen, Flc.TermVar_open_eq mlen]
  | .typeGen E', typeGen E'lc => rw [TermVar_open, E'lc.TermVar_open_eq mlen]
  | .typeApp E' A, typeApp E'lc => rw [TermVar_open, E'lc.TermVar_open_eq mlen]

theorem Term.TermVar_open_TermVar_subst_eq {E F : Term} (xnex' : x ≠ x')
  (Flc : F.TermVarLocallyClosed n)
  : (E.TermVar_open x n).TermVar_subst x' F = (E.TermVar_subst x' F).TermVar_open x n := by
  match E with
  | var x'' =>
    rw [TermVar_open, TermVar_subst, TermVar_subst]
    split
    · case isTrue h =>
      rw [← h, if_neg fun x => xnex' <| TermVar.free.inj x.symm, if_neg (nomatch ·), TermVar_open,
          if_pos rfl]
    · case isFalse h =>
      split
      · case isTrue h' => rw [Flc.TermVar_open_eq (Nat.le_refl _)]
      · case isFalse h' => rw [TermVar_open, if_neg h]
  | lam A E' =>
    rw [TermVar_open, TermVar_subst, TermVar_subst, TermVar_open,
        E'.TermVar_open_TermVar_subst_eq xnex' Flc.weaken]
  | app E' F =>
    rw [TermVar_open, TermVar_subst, TermVar_subst, TermVar_open,
        E'.TermVar_open_TermVar_subst_eq xnex' Flc,
        F.TermVar_open_TermVar_subst_eq xnex' Flc]
  | typeGen E' =>
    rw [TermVar_open, TermVar_subst, TermVar_subst, TermVar_open,
        E'.TermVar_open_TermVar_subst_eq xnex' Flc]
  | typeApp E' A =>
    rw [TermVar_open, TermVar_subst, TermVar_subst, TermVar_open,
        E'.TermVar_open_TermVar_subst_eq xnex' Flc]

theorem Term.TermVar_open_Term_open_eq {E F : Term} (Flc : F.TermVarLocallyClosed m) (mnen : m ≠ n)
  : (E.TermVar_open x m).Term_open F n = (E.Term_open F n).TermVar_open x m := by
  match E with
  | var (.free _) =>
    rw [TermVar_open, if_neg (nomatch ·), Term_open, if_neg (nomatch ·), TermVar_open,
        if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [TermVar_open]
    split
    · case isTrue h =>
      rw [Term_open, if_neg (nomatch ·), Term_open, ← h, if_neg (mnen <| TermVar.bound.inj ·.symm),
          TermVar_open, if_pos rfl]
    · case isFalse h =>
      rw [Term_open]
      split
      · case isTrue h' => rw [Flc.TermVar_open_eq (Nat.le_refl _)]
      · case isFalse h' => rw [TermVar_open, if_neg h]
  | lam A E' =>
    rw [TermVar_open, Term_open]
    simp only
    rw [TermVar_open_Term_open_eq Flc.weaken (by exact mnen <| Nat.succ_inj'.mp ·), ← TermVar_open,
        ← Term_open]
  | app E' F =>
    rw [TermVar_open, Term_open, TermVar_open_Term_open_eq Flc mnen,
        TermVar_open_Term_open_eq Flc mnen, ← TermVar_open, ← Term_open]
  | typeGen E' =>
    rw [TermVar_open, Term_open, TermVar_open_Term_open_eq Flc mnen, ← TermVar_open, ← Term_open]
  | typeApp E' A =>
    rw [TermVar_open, Term_open, TermVar_open_Term_open_eq Flc mnen, ← TermVar_open, ← Term_open]

theorem Term.TermVar_open_TypeVar_open_eq (E : Term)
  : (E.TermVar_open x m).TypeVar_open a n = (E.TypeVar_open a n).TermVar_open x m := by match E with
  | var (.free _) =>
    rw [TermVar_open, if_neg (nomatch ·), TypeVar_open, TermVar_open, if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [TermVar_open]
    split
    · case isTrue h => rw [← h, TypeVar_open, TypeVar_open, TermVar_open, if_pos rfl]
    · case isFalse h => rw [TypeVar_open, TermVar_open, if_neg h]
  | lam A E' =>
    rw [TermVar_open, TypeVar_open, TermVar_open_TypeVar_open_eq, ← TermVar_open, ← TypeVar_open]
  | app E' F =>
    rw [TermVar_open, TypeVar_open, TermVar_open_TypeVar_open_eq, TermVar_open_TypeVar_open_eq,
        ← TermVar_open, ← TypeVar_open]
  | typeGen E' =>
    rw [TermVar_open, TypeVar_open]
    simp only
    rw [TermVar_open_TypeVar_open_eq, ← TermVar_open, ← TypeVar_open]
  | typeApp E' A =>
    rw [TermVar_open, TypeVar_open, TermVar_open_TypeVar_open_eq, ← TermVar_open, ← TypeVar_open]

theorem Term.TypeVar_open_Type'_open_eq {E : Term} {A : Type'} (Alc : A.TypeVarLocallyClosed m)
  (mnen : m ≠ n) : (E.TypeVar_open a m).Type'_open A n = (E.Type'_open A n).TypeVar_open a m := by
  match E with
  | var _ => rw [TypeVar_open, Type'_open, TypeVar_open]
  | lam A E' =>
    rw [TypeVar_open, Type'_open, TypeVar_open_Type'_open_eq Alc mnen,
        Type'.TypeVar_open_Type'_open_eq Alc mnen, ← TypeVar_open, ← Type'_open]
  | app E' F =>
    rw [TypeVar_open, Type'_open, TypeVar_open_Type'_open_eq Alc mnen,
        TypeVar_open_Type'_open_eq Alc mnen, ← TypeVar_open, ← Type'_open]
  | typeGen E' =>
    rw [TypeVar_open, Type'_open]
    simp only
    rw [TypeVar_open_Type'_open_eq Alc.weaken (by exact mnen <| Nat.succ_inj'.mp ·), ← TypeVar_open,
        ← Type'_open]
  | typeApp E' A =>
    rw [TypeVar_open, Type'_open, TypeVar_open_Type'_open_eq Alc mnen,
        Type'.TypeVar_open_Type'_open_eq Alc mnen, ← TypeVar_open, ← Type'_open]

inductive Term.TypeVarLocallyClosed : Term → Nat → Prop where
  | var : TypeVarLocallyClosed (.var _) n
  | lam : A.TypeVarLocallyClosed n → E.TypeVarLocallyClosed n → TypeVarLocallyClosed (lam A E) n
  | app {E F : Term}
    : E.TypeVarLocallyClosed n → F.TypeVarLocallyClosed n → TypeVarLocallyClosed (E.app F) n
  | typeGen {E : Term} : E.TypeVarLocallyClosed (n + 1) → TypeVarLocallyClosed E.typeGen n
  | typeApp {E : Term}
    : E.TypeVarLocallyClosed n → A.TypeVarLocallyClosed n → TypeVarLocallyClosed (E.typeApp A) n

theorem Term.TypeVarLocallyClosed.weaken {E : Term}
  : E.TypeVarLocallyClosed m → E.TypeVarLocallyClosed (m + n)
  | var => var
  | lam Alc E'lc => lam Alc.weaken E'lc.weaken
  | app E'lc Flc => app E'lc.weaken Flc.weaken
  | typeGen E'lc => by
    apply typeGen
    rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc]
    exact E'lc.weaken
  | typeApp E'lc Alc => .typeApp E'lc.weaken Alc.weaken

theorem Term.TypeVarLocallyClosed.TermVar_open_drop {E : Term}
  : (E.TermVar_open x m).TypeVarLocallyClosed n → E.TypeVarLocallyClosed n := fun Elc => by
  match E with
  | .var _ => exact var
  | .lam A' E' =>
    rw [TermVar_open] at Elc
    let .lam A'lc E'lc := Elc
    exact lam A'lc E'lc.TermVar_open_drop
  | .app E' F =>
    rw [TermVar_open] at Elc
    let .app E'lc Flc := Elc
    exact app E'lc.TermVar_open_drop Flc.TermVar_open_drop
  | .typeGen E' =>
    rw [TermVar_open] at Elc
    let .typeGen E'lc := Elc
    exact typeGen E'lc.TermVar_open_drop
  | .typeApp E' A =>
    rw [TermVar_open] at Elc
    let .typeApp E'lc A'lc := Elc
    exact typeApp E'lc.TermVar_open_drop A'lc

theorem Term.TypeVarLocallyClosed.TypeVar_open_drop {E : Term} (h : m < n)
  : (E.TypeVar_open a m).TypeVarLocallyClosed n → E.TypeVarLocallyClosed n := fun Elc => by
  match E with
  | .var _ => exact var
  | .lam A' E' =>
    rw [TypeVar_open] at Elc
    let .lam A'lc E'lc := Elc
    exact lam (A'lc.TypeVar_open_drop h) (E'lc.TypeVar_open_drop h)
  | .app E' F =>
    rw [TypeVar_open] at Elc
    let .app E'lc Flc := Elc
    exact app (E'lc.TypeVar_open_drop h) (Flc.TypeVar_open_drop h)
  | .typeGen E' =>
    rw [TypeVar_open] at Elc
    let .typeGen E'lc := Elc
    exact typeGen <| E'lc.TypeVar_open_drop <| Nat.add_lt_add_iff_right.mpr h
  | .typeApp E' A =>
    rw [TypeVar_open] at Elc
    let .typeApp E'lc A'lc := Elc
    exact typeApp (E'lc.TypeVar_open_drop h) (A'lc.TypeVar_open_drop h)

theorem Term.TypeVarLocallyClosed.TypeVar_open_eq {E : Term} (h : E.TypeVarLocallyClosed m)
  (mlen : m ≤ n) : E.TypeVar_open x n = E := by match E, h with
  | .var _, var => rw [TypeVar_open]
  | .lam A E', lam Alc E'lc =>
    rw [TypeVar_open, Alc.TypeVar_open_eq mlen, E'lc.TypeVar_open_eq mlen]
  | .app E' F, app E'lc Flc =>
    rw [TypeVar_open, E'lc.TypeVar_open_eq mlen, Flc.TypeVar_open_eq mlen]
  | .typeGen E', typeGen E'lc =>
    rw [TypeVar_open]
    simp only
    rw [E'lc.TypeVar_open_eq (Nat.add_le_add_iff_right.mpr mlen)]
  | .typeApp E' A, typeApp E'lc Alc =>
    rw [TypeVar_open, E'lc.TypeVar_open_eq mlen, Alc.TypeVar_open_eq mlen]

theorem Term.TypeVar_open_TermVar_subst_eq {E F : Term} (Flc : F.TypeVarLocallyClosed n)
  : (E.TypeVar_open x n).TermVar_subst x' F = (E.TermVar_subst x' F).TypeVar_open x n := by
  match E with
  | var x'' =>
    rw [TypeVar_open, TermVar_subst]
    split
    · case isTrue h => exact Flc.TypeVar_open_eq (Nat.le_refl _) |>.symm
    · case isFalse h => rw [TypeVar_open]
  | lam A E' =>
    rw [TypeVar_open, TermVar_subst, TermVar_subst, TypeVar_open,
        E'.TypeVar_open_TermVar_subst_eq Flc]
  | app E' F =>
    rw [TypeVar_open, TermVar_subst, TermVar_subst, TypeVar_open,
        E'.TypeVar_open_TermVar_subst_eq Flc, F.TypeVar_open_TermVar_subst_eq Flc]
  | typeGen E' =>
    rw [TypeVar_open, TermVar_subst, TermVar_subst, TypeVar_open,
        E'.TypeVar_open_TermVar_subst_eq Flc.weaken]
  | typeApp E' A =>
    rw [TypeVar_open, TermVar_subst, TermVar_subst, TypeVar_open,
        E'.TypeVar_open_TermVar_subst_eq Flc]

theorem Term.TypeVar_open_Term_open_eq {E F : Term} (Flc : F.TypeVarLocallyClosed n)
  : (E.TypeVar_open x n).Term_open F m = (E.Term_open F m).TypeVar_open x n := by match E with
  | var (.free _) => rw [TypeVar_open, Term_open, if_neg (nomatch ·), TypeVar_open]
  | var (.bound _) =>
    rw [TypeVar_open, Term_open]
    split
    · case isTrue h => rw [Flc.TypeVar_open_eq (Nat.le_refl _)]
    · case isFalse h => rw [TypeVar_open]
  | lam A E' =>
    rw [TypeVar_open, Term_open]
    simp only
    rw [TypeVar_open_Term_open_eq Flc, Term_open, TypeVar_open]
  | app E' F =>
    rw [TypeVar_open, Term_open, TypeVar_open_Term_open_eq Flc, TypeVar_open_Term_open_eq Flc,
        ← TypeVar_open, ← Term_open]
  | typeGen E' =>
    rw [TypeVar_open, Term_open, TypeVar_open_Term_open_eq Flc.weaken, ← TypeVar_open, Term_open]
  | typeApp E' A =>
    rw [TypeVar_open, Term_open, TypeVar_open_Term_open_eq Flc, ← TypeVar_open, Term_open]

private
def Environment.appendExpr : Expr := .const `LottExamples.SystemF.Environment.append []

private
def Environment.TypeVar_substExpr : Expr :=
  .const `LottExamples.SystemF.Environment.TypeVar_subst []

nosubst
nonterminal Environment, G, D :=
  | "ε"                  : empty
  | G ", " x " : " A     : termVarExt (id x)
  | G ", " a             : typeVarExt (id a)
  | G ", " D             : append (elab := return mkApp2 Environment.appendExpr G D)
  | "(" G ")"            : paren (desugar := return G)
  | G " [" A " / " a "]" : subst (id a) (elab := return mkApp3 Environment.TypeVar_substExpr G a A)

namespace Environment

def append (G : Environment) : Environment → Environment
  | empty => G
  | termVarExt G' x A => G.append G' |>.termVarExt x A
  | typeVarExt G' a => G.append G' |>.typeVarExt a

theorem append_termVarExt : [[(G, G', x : A)]] = [[((G, G'), x : A)]] := rfl

theorem append_typeVarExt : [[(G, G', a)]] = [[((G, G'), a)]] := rfl

theorem empty_append (G : Environment) : empty.append G = G := match G with
  | empty => rfl
  | termVarExt G' x A => by rw [append_termVarExt, empty_append G']
  | typeVarExt G' a => by rw [append_typeVarExt, empty_append G']

theorem append_empty (G : Environment) : G.append empty = G := by match G with
  | empty => rfl
  | termVarExt G' x A => rw [append]
  | typeVarExt G' a => rw [append]

theorem append_assoc : [[(G, G', G'')]] = [[((G, G'), G'')]] := match G'' with
  | empty => rfl
  | termVarExt G''' x A => by
    rw [append_termVarExt, append_termVarExt, G.append_assoc, append_termVarExt]
  | typeVarExt G''' a => by
    rw [append_typeVarExt, append_typeVarExt, G.append_assoc, append_typeVarExt]

def TypeVar_subst (G : Environment) (a : TypeVarId) (A : Type') := match G with
  | empty => empty
  | termVarExt G' x A' => G'.TypeVar_subst a A |>.termVarExt x <| A'.TypeVar_subst a A
  | typeVarExt G' a' => G'.TypeVar_subst a A |>.typeVarExt a'

def termVar_count : Environment → Nat
  | empty => 0
  | termVarExt G _ _ => 1 + G.termVar_count
  | typeVarExt G _ => G.termVar_count

def typeVar_count : Environment → Nat
  | empty => 0
  | termVarExt G _ _ => G.typeVar_count
  | typeVarExt G _ => 1 + G.typeVar_count

def termVar_domain : Environment → List TermVarId
  | empty => []
  | termVarExt G x _ => x :: G.termVar_domain
  | typeVarExt G _ => G.termVar_domain

theorem termVar_domain_append
  : [[(G, G')]].termVar_domain = G'.termVar_domain ++ G.termVar_domain := by match G' with
  | empty => rw [termVar_domain, append_empty, List.nil_append]
  | termVarExt G'' x A =>
    rw [append_termVarExt, termVar_domain, termVar_domain, termVar_domain_append, List.cons_append]
  | typeVarExt G'' a =>
    rw [append_typeVarExt, termVar_domain, termVar_domain, termVar_domain_append]

def typeVar_domain : Environment → List TypeVarId
  | empty => []
  | termVarExt G _ _ => G.typeVar_domain
  | typeVarExt G a => a :: G.typeVar_domain

theorem typeVar_domain_append
  : [[(G, G')]].typeVar_domain = G'.typeVar_domain ++ G.typeVar_domain := by match G' with
  | empty => rw [typeVar_domain, append_empty, List.nil_append]
  | termVarExt G'' x A =>
    rw [append_termVarExt, typeVar_domain, typeVar_domain, typeVar_domain_append]
  | typeVarExt G'' a =>
    rw [append_typeVarExt, typeVar_domain, typeVar_domain, typeVar_domain_append, List.cons_append]

end Environment

nonterminal (parent := Term) Value, V :=
  | "λ " x " : " A ". " E : lam (bind x in E)
  | "Λ " a ". " E         : typeGen (bind a in E)

judgement_syntax a " ≠ " b : TypeVarNe (id a, b)

def TypeVarNe := Ne (α := TypeVarId)

judgement_syntax a " ∈ " G : TypeVarInEnvironment (id a)

judgement TypeVarInEnvironment :=

──────── head
a ∈ G, a

a ∈ G
──────────── termVarExt
a ∈ G, x : A

a ∈ G
a ≠ a'
───────── typeVarExt
a ∈ G, a'

judgement_syntax a " ∉ " G : TypeVarNotInEnvironment (id a)

def TypeVarNotInEnvironment a G := ¬[[a ∈ G]]

namespace TypeVarInEnvironment

theorem append_elim (ainGappGG : [[a ∈ G, GG]]) : [[a ∈ G]] ∨ [[a ∈ GG]] := by
  by_cases [[a ∈ GG]]
  · case pos ainGG => exact .inr ainGG
  · case neg aninGG =>
    left
    induction GG
    · case empty => exact ainGappGG
    · case termVarExt GG' x A ih =>
      apply ih
      · cases ainGappGG
        case ainGappGG.termVarExt => assumption
      · intro ainGG'
        exact aninGG ainGG'.termVarExt
    · case typeVarExt GG' a' ih =>
      by_cases a' = a
      · case pos a'eqa =>
        apply False.elim
        apply aninGG
        rw [a'eqa]
        exact head
      · case neg a'nea =>
        apply ih
        · cases ainGappGG
          · case ainGappGG.head => contradiction
          · case ainGappGG.typeVarExt => assumption
        · intro ainGG'
          apply aninGG
          have a'nea : a' ≠ a := a'nea
          exact ainGG'.typeVarExt a'nea.symm

theorem append_inl (ainG : [[a ∈ G]]) : [[a ∈ G, GG]] := by
  match GG with
  | .empty => exact ainG
  | .termVarExt GG' x A => exact ainG.append_inl |>.termVarExt
  | .typeVarExt GG' a' =>
    by_cases a' = a
    · case pos a'eqa =>
      rw [a'eqa]
      exact .head
    · case neg a'nea =>
      have a'nea : a' ≠ a := a'nea
      exact .typeVarExt ainG.append_inl a'nea.symm

theorem append_inr : [[a ∈ GG]] → [[a ∈ G, GG]]
  | head => head
  | termVarExt ainGG' => ainGG'.append_inr |>.termVarExt
  | typeVarExt ainGG' anea' => ainGG'.append_inr |>.typeVarExt anea'

theorem TypeVar_subst : [[a ∈ G]] → [[a ∈ G [A / a'] ]]
  | termVarExt ainG' => by
    rw [Environment.TypeVar_subst]
    exact termVarExt <| ainG'.TypeVar_subst
  | typeVarExt ainG' anea'' => by
    rw [Environment.TypeVar_subst]
    exact typeVarExt (ainG'.TypeVar_subst) anea''
  | head => by
    rw [Environment.TypeVar_subst]
    exact head

end TypeVarInEnvironment

namespace TypeVarNotInEnvironment

theorem termVarExt : [[a ∉ G]] → [[a ∉ G, x : A]]
  | aninG, .termVarExt ainG => aninG ainG

theorem typeVarExt (h : a ≠ a') : [[a ∉ G]] → [[a ∉ G, a']]
  | _, .head => h rfl
  | aninG, .typeVarExt ainG _ => aninG ainG

end TypeVarNotInEnvironment

judgement_syntax x " ≠ " y : TermVarNe (id x, y)

def TermVarNe := Ne (α := TermVarId)

judgement_syntax x " : " A " ∈ " G : TermVarInEnvironment (id x)

judgement TermVarInEnvironment :=

──────────────── head
x : A ∈ G, x : A

x : A ∈ G
x ≠ x'
───────────────── termVarExt
x : A ∈ G, x' : B

x : A ∈ G
──────────── typeVarExt
x : A ∈ G, a

judgement_syntax x " ∉ " G : TermVarNotInEnvironment (id x)

def TermVarNotInEnvironment x G := ∀ A : Type', ¬[[x : A ∈ G]]

namespace TermVarInEnvironment

theorem append_elim (xAinGappGG : [[x : A ∈ G, GG]])
  : [[x : A ∈ G]] ∧ [[x ∉ GG]] ∨ [[x : A ∈ GG]] := by
  by_cases [[x : A ∈ GG]]
  · case pos xAinGG => exact .inr xAinGG
  · case neg xAninGG =>
    left
    match GG with
    | .empty =>
      constructor
      · exact xAinGappGG
      · intro A'
        intro xA'inε
        nomatch xA'inε
    | .termVarExt GG' x' A' =>
      by_cases x' = x
      · case pos x'eqx =>
        by_cases A' = A
        · case pos A'eqA =>
          rw [x'eqx, A'eqA] at xAinGappGG xAninGG
          exact xAninGG head |>.elim
        · case neg A'neA =>
          cases xAinGappGG
          · case head => contradiction
          · case termVarExt xAinGappGG' xnex' =>
            exact xnex' x'eqx.symm |>.elim
      · case neg x'nex =>
        cases xAinGappGG
        · case head => contradiction
        · case termVarExt xAinGappGG' xnex' =>
          rcases xAinGappGG'.append_elim with ⟨xAinG, xninGG'⟩ | xAinG''
          · constructor
            · exact xAinG
            · intro A''
              intro xA''inGG'x'A'
              match xA''inGG'x'A' with
              | head => contradiction
              | termVarExt xA''inG'  _ => exact xninGG' A'' xA''inG'
          · have x'nex : x' ≠ x := x'nex
            exact False.elim <| xAninGG <| xAinG''.termVarExt x'nex.symm
    | .typeVarExt GG' a =>
      cases xAinGappGG
      case typeVarExt xAinGappG'' =>
      match xAinGappG''.append_elim with
      | .inl ⟨xAinG, xninGG'⟩ =>
        constructor
        · exact xAinG
        · intro A' xA'inGG'a
          apply xninGG' A'
          cases xA'inGG'a
          case right.typeVarExt xA'inGG' =>
          exact xA'inGG'
      | .inr xAinGG' =>
        exact xAninGG xAinGG'.typeVarExt |>.elim

theorem append_inl (xAinG : [[x : A ∈ G]]) (xninGG : [[x ∉ GG]]) : [[x : A ∈ G, GG]] := by
  match GG with
  | .empty => exact xAinG
  | .termVarExt GG' x' A' =>
    by_cases x' = x
    · case pos x'eqx =>
      rw [x'eqx]
      rw [x'eqx] at xninGG
      exact False.elim <| xninGG A' head
    · case neg x'nex =>
      have x'nex : x' ≠ x := x'nex
      apply TermVarInEnvironment.termVarExt _ x'nex.symm
      apply xAinG.append_inl
      intro A'' xA''inGG'
      apply xninGG A''
      exact termVarExt xA''inGG' x'nex.symm
  | .typeVarExt GG' a =>
    apply TermVarInEnvironment.typeVarExt
    apply xAinG.append_inl
    intro A' xA'inGG'
    exact xninGG A' xA'inGG'.typeVarExt

theorem append_inr : [[x : A ∈ GG]] → [[x : A ∈ G, GG]]
  | head => head
  | termVarExt xAinGG' xnex' => xAinGG'.append_inr |>.termVarExt xnex'
  | typeVarExt xAinGG' => xAinGG'.append_inr |>.typeVarExt

end TermVarInEnvironment

namespace TermVarNotInEnvironment

theorem termVarExt (xnex' : x ≠ x') : [[x ∉ G]] → [[x ∉ G, x' : A]] := fun xnin A xAinGx'A => by
  apply xnin A
  cases xAinGx'A
  · case head => contradiction
  · case termVarExt h _ => exact h

theorem typeVarExt : [[x ∉ G]] → [[x ∉ G, a]] := fun xnin A xAinGa => by
  apply xnin A
  cases xAinGa
  case typeVarExt h =>
  exact h

end TermVarNotInEnvironment

judgement_syntax a " ∈ " "ftv" "(" A ")" : InTypeFreeTypeVars (id a)

judgement InTypeFreeTypeVars :=

────────── var
a ∈ ftv(a)

a ∈ ftv(A)
────────────── arrl
a ∈ ftv(A → B)

a ∈ ftv(B)
────────────── arrr
a ∈ ftv(A → B)

a ∈ ftv(A)
─────────────── forall'
a ∈ ftv(∀ b. A)

namespace InTypeFreeTypeVars

theorem of_TypeVar_open {A : Type'} (h : a ≠ a')
  : InTypeFreeTypeVars a (A.TypeVar_open a' n) → [[a ∈ ftv(A)]] := fun ainAop => by
  match A with
  | .var (.free _) =>
    rw [Type'.TypeVar_open] at ainAop
    let .var := ainAop
    exact .var
  | .var (.bound _) =>
    rw [Type'.TypeVar_open] at ainAop
    split at ainAop
    · case isTrue h =>
      cases ainAop
      contradiction
    · case isFalse h =>
      nomatch ainAop
  | .arr A' B =>
    rw [Type'.TypeVar_open] at ainAop
    match ainAop with
    | .arrl ainA'op => exact .arrl <| ainA'op.of_TypeVar_open h
    | .arrr ainA'op => exact .arrr <| ainA'op.of_TypeVar_open h
  | .forall' A' =>
    rw [Type'.TypeVar_open] at ainAop
    let .forall' ainA'op := ainAop
    exact .forall' <| ainA'op.of_TypeVar_open h

theorem exists_gt (A : Type') : ∃ a : Nat, ∀ a' : Nat, [[a' ∈ ftv(A)]] → a' < a := match A with
  | .var (.free (x : Nat)) =>
    .intro (x + 1) fun | x', .var => Nat.lt_succ_self _
  | .var (.bound _) => .intro 0 fun _ x'in => nomatch x'in
  | .arr E' F =>
    let ⟨xE', xE'gt⟩ := exists_gt E'
    let ⟨xF, xFgt⟩ := exists_gt F
    .intro (max xE' xF) fun
      | x', .arrl x'infvE' =>
        Nat.lt_of_lt_of_le (xE'gt x' x'infvE') <| Nat.le_max_left _ _
      | x', .arrr x'infvF =>
        Nat.lt_of_lt_of_le (xFgt x' x'infvF) <| Nat.le_max_right _ _
  | .forall' E' =>
    let ⟨xE', xE'gt⟩ := exists_gt E'
    .intro xE' fun | _, .forall' x'infvE' => xE'gt _ x'infvE'

end InTypeFreeTypeVars

judgement_syntax a " ∉ " "ftv" "(" A ")" : NotInTypeFreeTypeVars (id a)

def NotInTypeFreeTypeVars a A := ¬[[a ∈ ftv(A)]]

namespace NotInTypeFreeTypeVars

theorem arr : [[a ∉ ftv(A → B)]] ↔ [[a ∉ ftv(A)]] ∧ [[a ∉ ftv(B)]] where
  mp anin := ⟨(anin <| .arrl ·), (anin <| .arrr ·)⟩
  mpr
    | ⟨aninA, _⟩, .arrl ainA => aninA ainA
    | ⟨_, aninB⟩, .arrr ainB => aninB ainB

theorem forall' : [[a ∉ ftv(∀ b. A)]] → [[a ∉ ftv(A)]] := (· <| .forall' ·)

theorem TypeVar_open_of_ne (h : a ≠ a') : [[a ∉ ftv(A)]] → [[a ∉ ftv(A^a')]] :=
  (· <| ·.of_TypeVar_open h)

theorem TypeVar_open_inj_of {A B : Type'} (aninftvA : [[a ∉ ftv(A)]]) (aninftvB : [[a ∉ ftv(B)]])
  : A.TypeVar_open a n = B.TypeVar_open a n → A = B := fun AopeqBop => by
  match A, B with
  | .var (.free _), .var (.free _) =>
    rw [Type'.TypeVar_open, if_neg (nomatch ·), Type'.TypeVar_open, if_neg (nomatch ·)] at AopeqBop
    exact AopeqBop
  | .var (.free _), .var (.bound _) =>
    rw [Type'.TypeVar_open, if_neg (nomatch ·), Type'.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [Type'.var.inj AopeqBop] at aninftvA
      exact aninftvA .var |>.elim
    · case isFalse h => nomatch AopeqBop
  | .var (.bound _), .var (.free _) =>
    rw [Type'.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [Type'.TypeVar_open, if_neg (nomatch ·)] at AopeqBop
      rw [← Type'.var.inj AopeqBop] at aninftvB
      exact aninftvB .var |>.elim
    · case isFalse h => nomatch AopeqBop
  | .var (.bound _), .var (.bound _) =>
    rw [Type'.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [← h]
      rw [Type'.TypeVar_open] at AopeqBop
      split at AopeqBop
      · case isTrue h' => rw [← h']
      · case isFalse h' => nomatch AopeqBop
    · case isFalse h =>
      rw [Type'.TypeVar_open] at AopeqBop
      split at AopeqBop
      · case isTrue h' => nomatch AopeqBop
      · case isFalse h' => exact AopeqBop
  | .arr A' B', .arr A'' B'' =>
    rw [Type'.TypeVar_open, Type'.TypeVar_open] at AopeqBop
    let ⟨A'opeqA''op, B'opeqB''op⟩ := Type'.arr.inj AopeqBop
    rw [(NotInTypeFreeTypeVars.arr.mp aninftvA).left.TypeVar_open_inj_of
          (NotInTypeFreeTypeVars.arr.mp aninftvB).left A'opeqA''op,
        (NotInTypeFreeTypeVars.arr.mp aninftvA).right.TypeVar_open_inj_of
          (NotInTypeFreeTypeVars.arr.mp aninftvB).right B'opeqB''op]
  | .forall' A', .forall' A'' =>
    rw [Type'.TypeVar_open, Type'.TypeVar_open] at AopeqBop
    rw [aninftvA.forall'.TypeVar_open_inj_of aninftvB.forall' <| Type'.forall'.inj AopeqBop]

theorem Type'_open_inj_of {A B : Type'} (aninftvA : [[a ∉ ftv(A)]]) (aninftvB : [[a ∉ ftv(B)]])
  : A.TypeVar_open a n = B.TypeVar_open a n → A = B := fun AopeqBop => by
  match A, B with
  | .var (.free _), .var (.free _) =>
    rw [Type'.TypeVar_open, if_neg (nomatch ·), Type'.TypeVar_open, if_neg (nomatch ·)] at AopeqBop
    exact AopeqBop
  | .var (.free _), .var (.bound _) =>
    rw [Type'.TypeVar_open, if_neg (nomatch ·), Type'.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [Type'.var.inj AopeqBop] at aninftvA
      exact aninftvA .var |>.elim
    · case isFalse h => nomatch AopeqBop
  | .var (.bound _), .var (.free _) =>
    rw [Type'.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [Type'.TypeVar_open, if_neg (nomatch ·)] at AopeqBop
      rw [← Type'.var.inj AopeqBop] at aninftvB
      exact aninftvB .var |>.elim
    · case isFalse h => nomatch AopeqBop
  | .var (.bound _), .var (.bound _) =>
    rw [Type'.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [← h]
      rw [Type'.TypeVar_open] at AopeqBop
      split at AopeqBop
      · case isTrue h' => rw [← h']
      · case isFalse h' => nomatch AopeqBop
    · case isFalse h =>
      rw [Type'.TypeVar_open] at AopeqBop
      split at AopeqBop
      · case isTrue h' => nomatch AopeqBop
      · case isFalse h' => exact AopeqBop
  | .arr A' B', .arr A'' B'' =>
    rw [Type'.TypeVar_open, Type'.TypeVar_open] at AopeqBop
    let ⟨A'opeqA''op, B'opeqB''op⟩ := Type'.arr.inj AopeqBop
    rw [(NotInTypeFreeTypeVars.arr.mp aninftvA).left.TypeVar_open_inj_of
          (NotInTypeFreeTypeVars.arr.mp aninftvB).left A'opeqA''op,
        (NotInTypeFreeTypeVars.arr.mp aninftvA).right.TypeVar_open_inj_of
          (NotInTypeFreeTypeVars.arr.mp aninftvB).right B'opeqB''op]
  | .forall' A', .forall' A'' =>
    rw [Type'.TypeVar_open, Type'.TypeVar_open] at AopeqBop
    rw [aninftvA.forall'.TypeVar_open_inj_of aninftvB.forall' <| Type'.forall'.inj AopeqBop]

theorem TypeVar_open_TypeVar_subst_eq_Type'_open_of
  : [[a ∉ ftv(A)]] → (A.TypeVar_open a n).TypeVar_subst a B = A.Type'_open B n := fun aninftvA => by
  match A with
  | .var (.free _) =>
    rw [Type'.TypeVar_open, if_neg (nomatch ·), Type'.TypeVar_subst]
    split
    · case isTrue h =>
      rw [← h] at aninftvA
      exact aninftvA .var |>.elim
    · case isFalse h => rw [Type'.Type'_open, if_neg (nomatch ·)]
  | .var (.bound _) =>
    rw [Type'.TypeVar_open]
    split
    · case isTrue h => rw [Type'.TypeVar_subst, if_pos rfl, Type'.Type'_open, if_pos h]
    · case isFalse h => rw [Type'.TypeVar_subst, if_neg (nomatch ·), Type'.Type'_open, if_neg h]
  | .arr A' B' =>
    rw [Type'.TypeVar_open, Type'.TypeVar_subst,
        NotInTypeFreeTypeVars.arr.mp aninftvA |>.left.TypeVar_open_TypeVar_subst_eq_Type'_open_of,
        NotInTypeFreeTypeVars.arr.mp aninftvA |>.right.TypeVar_open_TypeVar_subst_eq_Type'_open_of,
        ← Type'.Type'_open]
  | .forall' A' =>
    rw [Type'.TypeVar_open, Type'.TypeVar_subst,
        aninftvA.forall'.TypeVar_open_TypeVar_subst_eq_Type'_open_of, ← Type'.Type'_open]

end NotInTypeFreeTypeVars

theorem TermVarInEnvironment.TypeVar_subst {A : Type'} (aninftvA : [[a ∉ ftv(A)]])
  : TermVarInEnvironment x (A.TypeVar_open a n) [[ε, a, G]] →
    TermVarInEnvironment x (A.Type'_open B n) [[(G [B / a])]] := fun xAopinεaG =>
  match G, xAopinεaG with
  | .empty, xAopinεaG => nomatch xAopinεaG
  | .termVarExt .., head => by
    rw [Environment.TypeVar_subst, aninftvA.TypeVar_open_TypeVar_subst_eq_Type'_open_of]
    exact head
  | .termVarExt G' x' A', termVarExt xAopinεaG' xnex' =>
    xAopinεaG'.TypeVar_subst aninftvA |>.termVarExt xnex'
  | .typeVarExt G' a', typeVarExt xAopinεaG' => xAopinεaG'.TypeVar_subst aninftvA |>.typeVarExt

judgement_syntax x " ∈ " "fv" "(" E ")" : InFreeTermVars (id x)

judgement InFreeTermVars :=

───────── var
x ∈ fv(x)

x ∈ fv(E)
────────────────── lam
x ∈ fv(λ y : A. E)

x ∈ fv(E)
─────────── appl
x ∈ fv(E F)

x ∈ fv(F)
─────────── appr
x ∈ fv(E F)

x ∈ fv(E)
────────────── typeGen
x ∈ fv(Λ a. E)

x ∈ fv(E)
───────────── typeApp
x ∈ fv(E [A])

namespace InFreeTermVars

theorem of_TermVar_open {E : Term} (h : x ≠ x')
  : InFreeTermVars x (E.TermVar_open x' n) → [[x ∈ fv(E)]] := fun xinEop => by
  match E with
  | .var (.free _) =>
    rw [Term.TermVar_open] at xinEop
    let .var := xinEop
    exact .var
  | .var (.bound _) =>
    rw [Term.TermVar_open] at xinEop
    split at xinEop
    · case isTrue h =>
      cases xinEop
      contradiction
    · case isFalse h =>
      nomatch xinEop
  | .lam A E' =>
    rw [Term.TermVar_open] at xinEop
    let .lam xinE'op := xinEop
    exact .lam <| xinE'op.of_TermVar_open h
  | .app E' F =>
    rw [Term.TermVar_open] at xinEop
    match xinEop with
    | .appl xinE'op => exact .appl <| xinE'op.of_TermVar_open h
    | .appr xinE'op => exact .appr <| xinE'op.of_TermVar_open h
  | .typeGen E' =>
    rw [Term.TermVar_open] at xinEop
    let .typeGen xinE'op := xinEop
    exact .typeGen <| xinE'op.of_TermVar_open h
  | .typeApp E' A =>
    rw [Term.TermVar_open] at xinEop
    let .typeApp xinE'op := xinEop
    exact .typeApp <| xinE'op.of_TermVar_open h

theorem of_TypeVar_open {E : Term}
  : InFreeTermVars x (E.TypeVar_open a n) → [[x ∈ fv(E)]] := fun xinEop => by
  match E with
  | .var _ =>
    rw [Term.TypeVar_open] at xinEop
    let .var := xinEop
    exact .var
  | .lam A E' =>
    rw [Term.TypeVar_open] at xinEop
    let .lam xinE'op := xinEop
    exact .lam xinE'op.of_TypeVar_open
  | .app E' F =>
    rw [Term.TypeVar_open] at xinEop
    match xinEop with
    | .appl xinE'op => exact .appl xinE'op.of_TypeVar_open
    | .appr xinE'op => exact .appr xinE'op.of_TypeVar_open
  | .typeGen E' =>
    rw [Term.TypeVar_open] at xinEop
    let .typeGen xinE'op := xinEop
    exact .typeGen xinE'op.of_TypeVar_open
  | .typeApp E' A =>
    rw [Term.TypeVar_open] at xinEop
    let .typeApp xinE'op := xinEop
    exact .typeApp xinE'op.of_TypeVar_open

theorem exists_gt (E : Term) : ∃ x : Nat, ∀ x' : Nat, [[x' ∈ fv(E)]] → x' < x := match E with
  | .var (.free (x : Nat)) =>
    .intro (x + 1) fun | x', .var => Nat.lt_succ_self _
  | .var (.bound _) => .intro 0 fun _ x'in => nomatch x'in
  | .lam _ E' =>
    let ⟨xE', xE'gt⟩ := exists_gt E'
    .intro xE' fun | _, .lam x'infvE' => xE'gt _ x'infvE'
  | .app E' F =>
    let ⟨xE', xE'gt⟩ := exists_gt E'
    let ⟨xF, xFgt⟩ := exists_gt F
    .intro (max xE' xF) fun
      | x', .appl x'infvE' =>
        Nat.lt_of_lt_of_le (xE'gt x' x'infvE') <| Nat.le_max_left _ _
      | x', .appr x'infvF =>
        Nat.lt_of_lt_of_le (xFgt x' x'infvF) <| Nat.le_max_right _ _
  | .typeGen E' =>
    let ⟨xE', xE'gt⟩ := exists_gt E'
    .intro xE' fun | _, .typeGen x'infvE' => xE'gt _ x'infvE'
  | .typeApp E' _ =>
    let ⟨xE', xE'gt⟩ := exists_gt E'
    .intro xE' fun | _, .typeApp x'infvE' => xE'gt _ x'infvE'

end InFreeTermVars

judgement_syntax x " ∉ " "fv" "(" E ")" : NotInFreeTermVars (id x)

def NotInFreeTermVars x E := ¬[[x ∈ fv(E)]]

namespace NotInFreeTermVars

theorem lam : [[x ∉ fv(λ y : A. E)]] → [[x ∉ fv(E)]] := (· <| .lam ·)

theorem app : [[x ∉ fv(E F)]] → ([[x ∉ fv(E)]] ∧ [[x ∉ fv(F)]]) :=
  fun xnin => ⟨(xnin <| .appl ·), (xnin <| .appr ·)⟩

theorem typeGen : [[x ∉ fv(Λ a. E)]] → [[x ∉ fv(E)]] := (· <| .typeGen ·)

theorem typeApp : [[x ∉ fv(E [A])]] → [[x ∉ fv(E)]] := (· <| .typeApp ·)

theorem TermVar_open_of_ne (h : x ≠ x') : [[x ∉ fv(E)]] → [[x ∉ fv(E^x')]] :=
  (· <| ·.of_TermVar_open h)

theorem TypeVar_open : [[x ∉ fv(E)]] → [[x ∉ fv(E^a)]] := (· ·.of_TypeVar_open)

theorem exists_fresh {I : List _} : ∃ x ∉ I, [[x ∉ fv(E)]] :=
  let ⟨xI, xIgt⟩ := I.exists_gt
  let ⟨xE, xEgt⟩ := InFreeTermVars.exists_gt E
  let xIE := max xI xE
  .intro xIE ⟨
    fun inI => Nat.not_le_of_lt (xIgt xIE inI) <| Nat.le_max_left _ _,
    fun inE => Nat.not_le_of_lt (xEgt xIE inE) <| Nat.le_max_right _ _
  ⟩

end NotInFreeTermVars

judgement_syntax a " ∈ " "ftv" "(" E ")" : InTermFreeTypeVars (id a)

judgement InTermFreeTypeVars :=

a ∈ ftv(A)
─────────────────── laml
a ∈ ftv(λ x : A. E)

a ∈ ftv(E)
─────────────────── lamr
a ∈ ftv(λ x : A. E)

a ∈ ftv(E)
──────────── appl
a ∈ ftv(E F)

a ∈ ftv(F)
──────────── appr
a ∈ ftv(E F)

a ∈ ftv(E)
─────────────── typeGen
a ∈ ftv(Λ a. E)

a ∈ ftv(E)
────────────── typeAppl
a ∈ ftv(E [A])

a ∈ ftv(A)
────────────── typeAppr
a ∈ ftv(E [A])

namespace InTermFreeTypeVars

theorem of_TermVar_open {E : Term} : InTermFreeTypeVars a (E.TermVar_open x n) → [[a ∈ ftv(E)]] :=
  fun ainEop => by
  match E with
  | .var _ => nomatch ainEop
  | .lam A E' =>
    rw [Term.TermVar_open] at ainEop
    match ainEop with
    | .laml ainA => exact .laml ainA
    | .lamr ainE' => exact .lamr ainE'.of_TermVar_open
  | .app E' F =>
    rw [Term.TermVar_open] at ainEop
    match ainEop with
    | .appl ainE' => exact .appl ainE'.of_TermVar_open
    | .appr ainF => exact .appr ainF.of_TermVar_open
  | .typeGen E' =>
    rw [Term.TermVar_open] at ainEop
    let .typeGen ainE' := ainEop
    exact .typeGen ainE'.of_TermVar_open
  | .typeApp E' A =>
    rw [Term.TermVar_open] at ainEop
    match ainEop with
    | .typeAppl ainE' => exact .typeAppl ainE'.of_TermVar_open
    | .typeAppr ainA => exact .typeAppr ainA

theorem of_TypeVar_open {E : Term} (h : a ≠ a')
  : InTermFreeTypeVars a (E.TypeVar_open a' n) → [[a ∈ ftv(E)]] := fun ainEop => by
  match E with
  | .var _ => nomatch ainEop
  | .lam A E' =>
    rw [Term.TypeVar_open] at ainEop
    match ainEop with
    | .laml ainA => exact .laml <| ainA.of_TypeVar_open h
    | .lamr ainE' => exact .lamr <| ainE'.of_TypeVar_open h
  | .app E' F =>
    rw [Term.TypeVar_open] at ainEop
    match ainEop with
    | .appl ainE' => exact .appl <| ainE'.of_TypeVar_open h
    | .appr ainF => exact .appr <| ainF.of_TypeVar_open h
  | .typeGen E' =>
    rw [Term.TypeVar_open] at ainEop
    let .typeGen ainE' := ainEop
    exact .typeGen <| ainE'.of_TypeVar_open h
  | .typeApp E' A =>
    rw [Term.TypeVar_open] at ainEop
    match ainEop with
    | .typeAppl ainE' => exact .typeAppl <| ainE'.of_TypeVar_open h
    | .typeAppr ainA => exact .typeAppr <| ainA.of_TypeVar_open h

theorem exists_gt (E : Term) : ∃ a : Nat, ∀ a' : Nat, [[a' ∈ ftv(E)]] → a' < a := match E with
  | .var _ => .intro 0 fun _ x'in => nomatch x'in
  | .lam A E' =>
    let ⟨aA, aAgt⟩ := InTypeFreeTypeVars.exists_gt A
    let ⟨aE', aE'gt⟩ := exists_gt E'
    .intro (max aA aE') fun
      | _, .laml a'infvA =>
        Nat.lt_of_lt_of_le (aAgt _ a'infvA) <| Nat.le_max_left _ _
      | _, .lamr a'infvE' =>
        Nat.lt_of_lt_of_le (aE'gt _ a'infvE') <| Nat.le_max_right _ _
  | .app E' F =>
    let ⟨aE', aE'gt⟩ := exists_gt E'
    let ⟨aF, aFgt⟩ := exists_gt F
    .intro (max aE' aF) fun
      | _, .appl a'infvE' =>
        Nat.lt_of_lt_of_le (aE'gt _ a'infvE') <| Nat.le_max_left _ _
      | _, .appr a'infvF =>
        Nat.lt_of_lt_of_le (aFgt _ a'infvF) <| Nat.le_max_right _ _
  | .typeGen E' =>
    let ⟨aE', aE'gt⟩ := exists_gt E'
    .intro aE' fun | _, .typeGen a'infvE' => aE'gt _ a'infvE'
  | .typeApp E' A =>
    let ⟨aE', aE'gt⟩ := exists_gt E'
    let ⟨aA, aAgt⟩ := InTypeFreeTypeVars.exists_gt A
    .intro (max aE' aA) fun
      | _, .typeAppl a'infvE' =>
        Nat.lt_of_lt_of_le (aE'gt _ a'infvE') <| Nat.le_max_left _ _
      | _, .typeAppr a'infvA =>
        Nat.lt_of_lt_of_le (aAgt _ a'infvA) <| Nat.le_max_right _ _

end InTermFreeTypeVars

judgement_syntax a " ∉ " "ftv" "(" E ")" : NotInTermFreeTypeVars (id a)

def NotInTermFreeTypeVars a E := ¬[[a ∈ ftv(E)]]

namespace NotInTermFreeTypeVars

theorem lam : [[a ∉ ftv(λ x : A. E)]] → [[a ∉ ftv(A)]] ∧ [[a ∉ ftv(E)]] :=
  fun anin => ⟨(anin <| .laml ·), (anin <| .lamr ·)⟩

theorem app : [[a ∉ ftv(E F)]] → [[a ∉ ftv(E)]] ∧ [[a ∉ ftv(F)]] :=
  fun anin => ⟨(anin <| .appl ·), (anin <| .appr ·)⟩

theorem typeGen : [[a ∉ ftv(Λ a. E)]] → [[a ∉ ftv(E)]] := (· <| .typeGen ·)

theorem typeApp : [[a ∉ ftv(E [A])]] → [[a ∉ ftv(E)]] ∧ [[a ∉ ftv(A)]] :=
  fun anin => ⟨(anin <| .typeAppl ·), (anin <| .typeAppr ·)⟩

theorem TermVar_open : [[a ∉ ftv(E)]] → [[a ∉ ftv(E^x)]] := (· <| ·.of_TermVar_open)

theorem TypeVar_open_of_ne (h : a ≠ a') : [[a ∉ ftv(E)]] → [[a ∉ ftv(E^a')]] :=
  (· <| ·.of_TypeVar_open h)

theorem exists_fresh {I : List _} : ∃ a ∉ I, [[a ∉ ftv(E)]] ∧ [[a ∉ ftv(A)]] :=
  let ⟨aI, aIgt⟩ := I.exists_gt
  let ⟨aE, aEgt⟩ := InTermFreeTypeVars.exists_gt E
  let ⟨aA, aAgt⟩ := InTypeFreeTypeVars.exists_gt A
  .intro (max aI (max aE aA) : Nat) ⟨
    fun inI => Nat.not_le_of_lt (aIgt _ inI) <| Nat.le_max_left _ _,
    fun inE => Nat.not_le_of_lt (aEgt _ inE) <|
      Nat.le_trans (Nat.le_max_left _ _) <| Nat.le_max_right _ _,
    fun inA => Nat.not_le_of_lt (aAgt _ inA) <|
      Nat.le_trans (Nat.le_max_right _ _) <| Nat.le_max_right _ _
  ⟩

end NotInTermFreeTypeVars

judgement_syntax G " ⊢ " A : TypeWellFormedness

judgement TypeWellFormedness :=

a ∈ G
───── var
G ⊢ a

G ⊢ A
G ⊢ B
───────── arr
G ⊢ A → B

∀ a ∉ (I : List _), G, a ⊢ A^a
────────────────────────────── forall'
G ⊢ ∀ a. A

namespace TypeWellFormedness

theorem TermVar_drop (Bwf : [[G, x : A, G' ⊢ B]]) : [[G, G' ⊢ B]] := match B, Bwf with
  | .var _, var ainGxAGG => match ainGxAGG.append_elim with
    | .inl (.termVarExt ainG) => var ainG.append_inl
    | .inr ainGG => var ainGG.append_inr
  | .arr .., arr A'wf B'wf => arr A'wf.TermVar_drop B'wf.TermVar_drop
  | .forall' _, forall' A'wf => forall' fun a anin => by
    have := A'wf a anin
    rw [← Environment.append_typeVarExt] at this
    exact this.TermVar_drop

theorem weakening (Awf : [[G ⊢ A]]) : [[G', G ⊢ A]] := match Awf with
  | var ain => var ain.append_inr
  | arr A'wf Bwf => arr A'wf.weakening Bwf.weakening
  | forall' (I := I) A'wf => forall' (I := I) fun a anin => A'wf a anin |>.weakening

theorem TypeVarLocallyClosed_of : [[G ⊢ A]] → A.TypeVarLocallyClosed G.typeVar_count := fun Awf =>
  match A, Awf with
  | _, .var _ => .var_free
  | .arr _ _, .arr A'wf Bwf => .arr A'wf.TypeVarLocallyClosed_of Bwf.TypeVarLocallyClosed_of
  | .forall' A', .forall' A'wf (I := I) => by
    let ⟨a, anin⟩ := I.exists_fresh
    have := A'wf a anin |>.TypeVarLocallyClosed_of
    rw [Environment.typeVar_count, Nat.add_comm] at this
    exact .forall' <| this.TypeVar_open_drop <| Nat.zero_lt_succ _

theorem TypeVarLocallyClosed_of_empty : [[ε ⊢ A]] → A.TypeVarLocallyClosed 0 :=
  TypeVarLocallyClosed_of

theorem Type'_open_preservation {A : Type'} {G : Environment} (aninftvA : [[a ∉ ftv(A)]])
  (Bwf : [[ε ⊢ B]])
  : TypeWellFormedness [[ε, a, G]] (A.TypeVar_open a n) →
    TypeWellFormedness [[(G [B / a])]] (A.Type'_open B n) :=
  fun Aopwf => by match A with
  | .var (.free a') =>
    rw [Type'.TypeVar_open, if_neg (nomatch ·)] at Aopwf
    let .var a'inaG := Aopwf
    match a'inaG.append_elim with
    | .inl .head => exact aninftvA .var |>.elim
    | .inr a'inG => exact .var a'inG.TypeVar_subst
  | .var (.bound _) =>
    rw [Type'.Type'_open]
    split
    · case isTrue h => exact Bwf.weakening
    · case isFalse h =>
      rw [Type'.TypeVar_open, if_neg h] at Aopwf
      nomatch Aopwf
  | .arr A' B' =>
    rw [Type'.TypeVar_open] at Aopwf
    let .arr A'wf B'wf := Aopwf
    exact .arr (Type'_open_preservation (NotInTypeFreeTypeVars.arr.mp aninftvA).left Bwf A'wf)
      (Type'_open_preservation (NotInTypeFreeTypeVars.arr.mp aninftvA).right Bwf B'wf)
  | .forall' A' =>
    rw [Type'.TypeVar_open] at Aopwf
    simp only at Aopwf
    let .forall' A'wf (I := I) := Aopwf
    exact .forall' (I := a :: I) <| fun a' a'nin => by
      have a'nea := List.ne_of_not_mem_cons a'nin
      have := A'wf a' <| List.not_mem_of_not_mem_cons a'nin
      rw [← A'.TypeVar_open_Type'_open_eq Bwf.TypeVarLocallyClosed_of_empty (Nat.zero_ne_add_one _),
          ← Environment.TypeVar_subst]
      rw [A'.TypeVar_open_comm a'nea.symm (Nat.succ_ne_zero _)] at this
      exact Type'_open_preservation (aninftvA.forall'.TypeVar_open_of_ne a'nea.symm) Bwf this

theorem TypeVar_subst_preservation {A : Type'} {G : Environment} (Bwf : [[ε ⊢ B]])
  : [[ε, a, G ⊢ A]] → [[G [B / a] ⊢ A [B / a] ]] :=
  fun Aopwf => by match A with
  | .var (.free a') =>
    let .var a'inεaG := Aopwf
    rw [Type'.TypeVar_subst]
    split
    · case isTrue h => exact Bwf.weakening
    · case isFalse h =>
      match a'inεaG.append_elim with
      | .inl .head => contradiction
      | .inr a'inG => exact TypeWellFormedness.var a'inG.TypeVar_subst
  | .var (.bound _) => nomatch Aopwf
  | .arr A' B' =>
    let .arr A'wf B'wf := Aopwf
    exact .arr (TypeWellFormedness.TypeVar_subst_preservation Bwf A'wf)
      (TypeWellFormedness.TypeVar_subst_preservation Bwf B'wf)
  | .forall' A' =>
    let .forall' A'wf (I := I) := Aopwf
    rw [Type'.TypeVar_subst]
    exact .forall' (I := a :: I) fun a' a'nin => by
      have a'nea := List.ne_of_not_mem_cons a'nin
      have := A'wf a' <| List.not_mem_of_not_mem_cons a'nin
      rw [← Environment.TypeVar_subst,
          Type'.TypeVar_subst_TypeVar_open_comm Bwf.TypeVarLocallyClosed_of_empty a'nea.symm]
      rw [← Environment.append_typeVarExt] at this
      exact TypeVar_subst_preservation Bwf this

end TypeWellFormedness

judgement_syntax x " ∈ " "dom" "(" G ")" : TermVarInEnvironmentDomain (id x)

def TermVarInEnvironmentDomain x (G : Environment) := x ∈ G.termVar_domain

judgement_syntax x " ∉ " "dom" "(" G ")" : TermVarNotInEnvironmentDomain (id x)

def TermVarNotInEnvironmentDomain x G := ¬[[x ∈ dom(G)]]

namespace TermVarNotInEnvironmentDomain

theorem TermVar_drop : [[x ∉ dom(ε, x' : A, G)]] → [[x ∉ dom(G)]] :=
  fun xnindomεxAG => by
  match G with
  | .empty => exact (nomatch ·)
  | .termVarExt G' x'' A' =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindomεxAG ⊢
    rw [Environment.termVar_domain_append] at xnindomεxAG
    let ⟨xnindomG, _⟩ := List.not_mem_append'.mp xnindomεxAG
    exact xnindomG
  | .typeVarExt G' a =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindomεxAG ⊢
    rw [Environment.termVar_domain_append] at xnindomεxAG
    let ⟨xnindomG, _⟩ := List.not_mem_append'.mp xnindomεxAG
    exact xnindomG

theorem TypeVar_drop : [[x ∉ dom(ε, a, G)]] → [[x ∉ dom(G)]] := fun xnindomεaG => by
  match G with
  | .empty => exact (nomatch ·)
  | .termVarExt G' x' A' =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindomεaG ⊢
    rw [Environment.termVar_domain_append] at xnindomεaG
    let ⟨xnindomG, _⟩ := List.not_mem_append'.mp xnindomεaG
    exact xnindomG
  | .typeVarExt G' a' =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindomεaG ⊢
    rw [Environment.termVar_domain_append] at xnindomεaG
    let ⟨xnindomG, _⟩ := List.not_mem_append'.mp xnindomεaG
    exact xnindomG

theorem TypeVar_subst : [[x ∉ dom(G)]] → [[x ∉ dom(G [A / a])]] := fun xnindom => by
  match G with
  | .empty => exact (nomatch ·)
  | .termVarExt G' x' A' =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindom ⊢
    rw [Environment.TypeVar_subst, Environment.termVar_domain]
    rw [Environment.termVar_domain] at xnindom
    let xnex' := List.ne_of_not_mem_cons xnindom
    let xnindomG' := List.not_mem_of_not_mem_cons xnindom
    have : [[x ∉ dom(G')]] := by
      dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain]
      exact xnindomG'
    exact List.not_mem_cons_of_ne_of_not_mem xnex' this.TypeVar_subst
  | .typeVarExt G' a' =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindom ⊢
    rw [Environment.TypeVar_subst, Environment.termVar_domain]
    rw [Environment.termVar_domain] at xnindom
    have : [[x ∉ dom(G')]] := by
      dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain]
      exact xnindom
    exact this.TypeVar_subst

end TermVarNotInEnvironmentDomain

judgement_syntax a " ∈ " "dom" "(" G ")" : TypeVarInEnvironmentDomain (id a)

def TypeVarInEnvironmentDomain a (G : Environment) := a ∈ G.typeVar_domain

judgement_syntax a " ∉ " "dom" "(" G ")" : TypeVarNotInEnvironmentDomain (id a)

def TypeVarNotInEnvironmentDomain a G := ¬[[a ∈ dom(G)]]

namespace TypeVarNotInEnvironmentDomain

theorem TermVar_drop : [[a ∉ dom(ε, x : A, G)]] → [[a ∉ dom(G)]] :=
  fun anindomεxAG => by
  match G with
  | .empty => exact (nomatch ·)
  | .termVarExt G' x' A' =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindomεxAG ⊢
    rw [Environment.typeVar_domain_append] at anindomεxAG
    let ⟨anindomG, _⟩ := List.not_mem_append'.mp anindomεxAG
    exact anindomG
  | .typeVarExt G' a =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindomεxAG ⊢
    rw [Environment.typeVar_domain_append] at anindomεxAG
    let ⟨anindomG, _⟩ := List.not_mem_append'.mp anindomεxAG
    exact anindomG

theorem TypeVar_drop : [[a ∉ dom(ε, a', G)]] → [[a ∉ dom(G)]] := fun anindomεa'G => by
  match G with
  | .empty => exact (nomatch ·)
  | .termVarExt G' x' A' =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindomεa'G ⊢
    rw [Environment.typeVar_domain_append] at anindomεa'G
    let ⟨anindomG, _⟩ := List.not_mem_append'.mp anindomεa'G
    exact anindomG
  | .typeVarExt G' a'' =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindomεa'G ⊢
    rw [Environment.typeVar_domain_append] at anindomεa'G
    let ⟨anindomG, _⟩ := List.not_mem_append'.mp anindomεa'G
    exact anindomG

theorem TypeVar_subst : [[a ∉ dom(G)]] → [[a ∉ dom(G [A / a'])]] := fun anindom => by
  match G with
  | .empty => exact (nomatch ·)
  | .termVarExt G' x' A' =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindom ⊢
    rw [Environment.TypeVar_subst, Environment.typeVar_domain]
    rw [Environment.typeVar_domain] at anindom
    have : [[a ∉ dom(G')]] := by
      dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain]
      exact anindom
    exact this.TypeVar_subst
  | .typeVarExt G' a' =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindom ⊢
    rw [Environment.TypeVar_subst, Environment.typeVar_domain]
    rw [Environment.typeVar_domain] at anindom
    let xnex' := List.ne_of_not_mem_cons anindom
    let anindomG' := List.not_mem_of_not_mem_cons anindom
    have : [[a ∉ dom(G')]] := by
      dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain]
      exact anindomG'
    exact List.not_mem_cons_of_ne_of_not_mem xnex' this.TypeVar_subst

end TypeVarNotInEnvironmentDomain

judgement_syntax "⊢ " G : EnvironmentWellFormedness

judgement EnvironmentWellFormedness :=

─── empty
⊢ ε

⊢ G
G ⊢ A
x ∉ dom(G)
────────── termVarExt
⊢ G, x : A

⊢ G
a ∉ dom(G)
────────── typeVarExt
⊢ G, a

namespace EnvironmentWellFormedness

theorem TermVar_drop : [[⊢ ε, x : A, G]] → [[⊢ G]] := fun εxAGwf => by match G, εxAGwf with
  | .empty, _ => exact empty
  | .termVarExt G' x' A', termVarExt G'wf A'wf x'nindom =>
    have := A'wf.TermVar_drop (G := .empty)
    rw [Environment.empty_append] at this
    exact termVarExt G'wf.TermVar_drop this x'nindom.TermVar_drop
  | .typeVarExt G' a, typeVarExt G'wf anindom => exact typeVarExt G'wf.TermVar_drop anindom.TermVar_drop

theorem TypeVar_subst_preservation (Awf : [[ε ⊢ A]]) : [[⊢ ε, a, G]] → [[⊢ G [A / a] ]] :=
  fun εaGwf => by
  match G, εaGwf with
  | .empty, _ =>
    rw [Environment.TypeVar_subst]
    exact .empty
  | .termVarExt G' x' A', termVarExt εaG'wf A'wf x'nindom =>
    rw [Environment.TypeVar_subst]
    exact termVarExt (εaG'wf.TypeVar_subst_preservation Awf) (.TypeVar_subst_preservation Awf A'wf)
      x'nindom.TypeVar_drop.TypeVar_subst
  | .typeVarExt G' a', typeVarExt εaG'wf a'nindom =>
    rw [Environment.TypeVar_subst]
    exact typeVarExt (εaG'wf.TypeVar_subst_preservation Awf) a'nindom.TypeVar_drop.TypeVar_subst

end EnvironmentWellFormedness

judgement_syntax G " ⊢ " E " : " A : Typing

judgement Typing :=

⊢ G
x : A ∈ G
───────── var
G ⊢ x : A

G ⊢ A
∀ x ∉ (I : List _), G, x : A ⊢ E^x : B
────────────────────────────────────── lam
G ⊢ λ x : A. E : A → B

G ⊢ E : A → B
G ⊢ F : A
───────────── app
G ⊢ E F : B

∀ a ∉ (I : List _), G, a ⊢ E^a : A^a
──────────────────────────────────── typeGen
G ⊢ Λ a. E : ∀ a. A

G ⊢ E : ∀ a. A
G ⊢ B
──────────────── typeApp
G ⊢ E [B] : A^^B

namespace Typing

theorem TermVarLocallyClosed_of_empty : [[ε ⊢ E : A]] → E.TermVarLocallyClosed 0 := go
where
  go {G : Environment} {E : Term} {A : Type'}
    : [[G ⊢ E : A]] → E.TermVarLocallyClosed G.termVar_count := fun EtyA => match E, EtyA with
    | _, .var .. => .var_free
    | .lam A' E', .lam _ E'ty (I := I) => by
      let ⟨x, xnin⟩ := I.exists_fresh
      have := go <| E'ty x xnin
      rw [Environment.termVar_count, Nat.add_comm] at this
      exact .lam <| this.TermVar_open_drop <| Nat.zero_lt_succ _
    | .app _ _, .app E'ty Fty => .app (go E'ty) (go Fty)
    | .typeGen E', .typeGen E'ty (I := I) => by
      let ⟨a, anin⟩ := I.exists_fresh
      exact .typeGen <| go (E'ty a anin) |>.TypeVar_open_drop
    | .typeApp E' _, .typeApp E'ty _ => .typeApp <| go E'ty

theorem TypeVarLocallyClosed_of_empty : [[ε ⊢ E : A]] → E.TypeVarLocallyClosed 0 := go
where
  go {G : Environment} {E : Term} {A : Type'}
    : [[G ⊢ E : A]] → E.TypeVarLocallyClosed G.typeVar_count := fun EtyA => match E, EtyA with
    | _, .var .. => .var
    | .lam A' E', .lam A'ty E'ty (I := I) => by
      let ⟨x, xnin⟩ := I.exists_fresh
      have := go <| E'ty x xnin
      rw [Environment.typeVar_count] at this
      exact .lam A'ty.TypeVarLocallyClosed_of this.TermVar_open_drop
    | .app _ _, .app E'ty Fty => .app (go E'ty) (go Fty)
    | .typeGen E', .typeGen E'ty (I := I) => by
      let ⟨a, anin⟩ := I.exists_fresh
      have := go <| E'ty a anin
      rw [Environment.typeVar_count, Nat.add_comm] at this
      apply Term.TypeVarLocallyClosed.typeGen
      exact this.TypeVar_open_drop <| Nat.zero_lt_succ _
    | .typeApp E' A', .typeApp E'ty A'ty => .typeApp (go E'ty) A'ty.TypeVarLocallyClosed_of

theorem weakening (EtyA : [[G ⊢ E : A]]) (G'Gwf : [[⊢ G', G]]) : [[G', G ⊢ E : A]] :=
  match EtyA with
  | var _ xin => var G'Gwf xin.append_inr
  | lam Awf E'ty (I := I) =>
    lam Awf.weakening (I := [[(G', G)]].termVar_domain ++ I) fun x xnin =>
      let ⟨xnindom, xninI⟩ := List.not_mem_append'.mp xnin
      E'ty x xninI |>.weakening <| G'Gwf.termVarExt Awf.weakening xnindom
  | app E'ty Fty => app (E'ty.weakening G'Gwf) (Fty.weakening G'Gwf)
  | typeGen E'ty (I := I) => typeGen (I := [[(G', G)]].typeVar_domain ++ I) fun a anin =>
      let ⟨anindom, aninI⟩ := List.not_mem_append'.mp anin
      E'ty a aninI |>.weakening <| G'Gwf.typeVarExt anindom
  | typeApp E'ty Bwf => typeApp (E'ty.weakening G'Gwf) Bwf.weakening

theorem Term_open_preservation {E : Term} (EtyB : Typing [[ε, x : A, G]] (E.TermVar_open x n) B)
  (xninG : [[x ∉ G]]) (xninfvE : [[x ∉ fv(E)]]) (FtyA : [[ε ⊢ F : A]])
  : Typing G (E.Term_open F n) B := by
  match E with
  | .var (.free _) =>
    rw [Term.Term_open, if_neg (nomatch ·)]
    let .var εxAGwf x'BinεxAG := EtyB
    match x'BinεxAG.append_elim with
    | .inl ⟨.head, _⟩ => exact xninfvE .var |>.elim
    | .inr xBinG => exact var εxAGwf.TermVar_drop xBinG
  | .var (.bound _) =>
    rw [Term.Term_open]
    split
    · case isTrue h =>
      rw [← h, Term.TermVar_open, if_pos rfl] at EtyB
      let .var εxAGwf xBinxAG := EtyB
      match xBinxAG.append_elim with
      | .inl ⟨.head, _⟩ => exact FtyA.weakening εxAGwf.TermVar_drop
      | .inr xBinG => exact xninG _ xBinG |>.elim
    · case isFalse h =>
      rw [Term.TermVar_open, if_neg h] at EtyB
      nomatch EtyB
  | .lam A' E' =>
    rw [Term.Term_open]
    simp only
    let .lam A'wf E'ty (I := I) := EtyB
    rw [← G.empty_append]
    exact lam (I := x :: I) A'wf.TermVar_drop fun x' x'nin => by
      have x'nex := List.ne_of_not_mem_cons x'nin
      have := E'ty x' <| List.not_mem_of_not_mem_cons x'nin
      rw [Environment.empty_append,
          ← E'.TermVar_open_Term_open_eq (n := n + 1) (m := 0)
            FtyA.TermVarLocallyClosed_of_empty (Nat.zero_ne_add_one _)]
      rw [← Environment.append_termVarExt,
          E'.TermVar_open_comm x'nex.symm (Nat.succ_ne_zero _)] at this
      exact this.Term_open_preservation (xninG.termVarExt x'nex.symm)
        (xninfvE.lam.TermVar_open_of_ne x'nex.symm) FtyA
  | .app E' F =>
    let .app E'ty Fty := EtyB
    rw [Term.Term_open]
    exact app (E'ty.Term_open_preservation xninG xninfvE.app.left FtyA)
      (Fty.Term_open_preservation xninG xninfvE.app.right FtyA)
  | .typeGen E' =>
    let .typeGen E'ty := EtyB
    rw [Term.Term_open]
    exact typeGen fun a anin => by
      have := E'ty a anin
      rw [← E'.TypeVar_open_Term_open_eq FtyA.TypeVarLocallyClosed_of_empty]
      rw [← Environment.append_typeVarExt, E'.TermVar_open_TypeVar_open_eq] at this
      exact this.Term_open_preservation xninG.typeVarExt
        xninfvE.typeGen.TypeVar_open FtyA
  | .typeApp E' A' =>
    let .typeApp E'ty A'wf := EtyB
    have := A'wf.TermVar_drop
    rw [G.empty_append] at this
    exact typeApp (E'ty.Term_open_preservation xninG xninfvE.typeApp FtyA) this

theorem Type'_open_preservation {E : Term} {A : Type'}
  (EtyA : Typing [[ε, a, G]] (E.TypeVar_open a n) (A.TypeVar_open a n)) (aninG : [[a ∉ G]])
  (aninftvE : [[a ∉ ftv(E)]]) (aninftvA : [[a ∉ ftv(A)]]) (Bwf : [[ε ⊢ B]])
  : Typing [[(G [B / a])]] (E.Type'_open B n) (A.Type'_open B n) := by
  generalize E'eq : E.TypeVar_open a n = E', A'eq : A.TypeVar_open a n = A' at *
  match E, A, EtyA with
  | .var (.free x), A, .var εaGwf xAopinεaG =>
    rw [Term.Type'_open]
    cases E'eq
    cases A'eq
    exact var (εaGwf.TypeVar_subst_preservation Bwf) <| xAopinεaG.TypeVar_subst aninftvA
  | .lam A'' E'', .arr A''' B', .lam A''wf E''ty (A := A'''') (B := B'') =>
    rw [Term.Type'_open, Type'.Type'_open]
    cases E'eq
    rw [Type'.TypeVar_open] at A'eq
    let ⟨A''opeq, B'opeq⟩ := Type'.arr.inj A'eq
    cases B'opeq
    cases NotInTypeFreeTypeVars.TypeVar_open_inj_of (NotInTypeFreeTypeVars.arr.mp aninftvA).left
      aninftvE.lam.left A''opeq
    exact Typing.lam (TypeWellFormedness.Type'_open_preservation aninftvE.lam.left Bwf A''wf)
      fun x' x'nin => by
        have := E''ty x' x'nin
        rw [← E''.TermVar_open_Type'_open_comm]
        rw [← Environment.append_termVarExt, ← Term.TermVar_open_TypeVar_open_eq] at this
        have := this.Type'_open_preservation aninG.termVarExt aninftvE.lam.right.TermVar_open
          (NotInTypeFreeTypeVars.arr.mp aninftvA).right Bwf
        rw [Environment.TypeVar_subst,
            aninftvE.lam.left.TypeVar_open_TypeVar_subst_eq_Type'_open_of] at this
        exact this
  | .app E'' F, A, .app E''ty Fty (A := A'') =>
    rw [Term.Type'_open]
    cases E'eq
    cases A'eq
    sorry
  | .typeGen E', .forall' A', .typeGen E'ty (I := I) =>
    cases E'eq
    cases A'eq
    exact .typeGen (I := a :: I) fun a' a'nin => by
      have a'nea := List.ne_of_not_mem_cons a'nin
      have := E'ty a' <| List.not_mem_of_not_mem_cons a'nin
      rw [← E'.TypeVar_open_Type'_open_eq Bwf.TypeVarLocallyClosed_of_empty (Nat.zero_ne_add_one _),
          ← A'.TypeVar_open_Type'_open_eq Bwf.TypeVarLocallyClosed_of_empty (Nat.zero_ne_add_one _)]
      rw [← Environment.append_typeVarExt, E'.TypeVar_open_comm a'nea.symm (Nat.succ_ne_zero _),
          A'.TypeVar_open_comm a'nea.symm (Nat.succ_ne_zero _)] at this
      exact this.Type'_open_preservation (G := G.typeVarExt a')
        (aninG.typeVarExt a'nea.symm)
        (aninftvE.typeGen.TypeVar_open_of_ne a'nea.symm)
        (aninftvA.forall'.TypeVar_open_of_ne a'nea.symm) Bwf
  | .typeApp E' B', A, .typeApp E'ty B'wf (A := A'') =>
    rw [Term.Type'_open]
    cases E'eq
    sorry
termination_by sizeOf E
decreasing_by all_goals sorry

end Typing

judgement_syntax E " -> " F : OperationalSemantics

judgement OperationalSemantics :=

E -> E'
─────────── appl
E F -> E' F

F -> F'
─────────── appr
V F -> V F'

────────────────────── lamApp
(λ x : A. E) V -> E^^V

E -> E'
─────────────── typeApp
E [A] -> E' [A]

──────────────────── typeGenApp
(Λ a. E) [A] -> E^^A

namespace OperationalSemantics

theorem preservation (EtyA : [[ε ⊢ E : A]]) (EstepF : [[E -> F]]) : [[ε ⊢ F : A]] :=
  match EstepF, EtyA with
  | appl E'stepE'next, .app E'tyA'arrA FtyA' =>.app (E'stepE'next.preservation E'tyA'arrA) FtyA'
  | appr FstepFnext, .app VtyA'arrA FtyA' => .app VtyA'arrA <| FstepFnext.preservation FtyA'
  | lamApp, .app (.lam _ E'tyA (E := E')) VtyA'' =>
    let ⟨x, xnin, xninfv⟩ := NotInFreeTermVars.exists_fresh
    .Term_open_preservation (E'tyA x xnin) (fun _ => (nomatch ·)) xninfv VtyA''
  | typeApp E'stepE'next, .typeApp E'ty A'wf => .typeApp (E'stepE'next.preservation E'ty) A'wf
  | typeGenApp, .typeApp (.typeGen E'tyA'') A'wf =>
    let ⟨a, anin, aninftvE', aninftvA''⟩ := NotInTermFreeTypeVars.exists_fresh
    .Type'_open_preservation (G := .empty) (E'tyA'' a anin) (nomatch ·) aninftvE' aninftvA'' A'wf

theorem progress (EtyA : [[ε ⊢ E : A]]) : (∃ F, [[E -> F]]) ∨ ∃ V : Value, V.val = E :=
  match E, EtyA with
  | .lam .., _ => .inr <| .intro ⟨_, .lam⟩ rfl
  | .app E' F', .app E'tyA'arrA F'tyA' => match progress E'tyA'arrA with
    | .inl ⟨E'_next, E'stepE'_next⟩ => .inl <| .intro _ <| appl E'stepE'_next
    | .inr ⟨VE', VE'eqE'⟩ => by
      match progress F'tyA' with
      | .inl ⟨F'_next, F'stepF'_next⟩ =>
        rw [← VE'eqE']
        exact .inl <| .intro _ <| appr F'stepF'_next
      | .inr ⟨VF', VF'eqF'⟩ =>
        have E'val := VE'.property
        rw [VE'eqE'] at E'val
        let .lam A' E'' := E'
        rw [← VF'eqF']
        exact .inl <| .intro _ lamApp
  | .typeGen _, _ => .inr <| .intro ⟨_, .typeGen⟩ rfl
  | .typeApp E' A', .typeApp E'ty _ => match progress E'ty with
    | .inl ⟨E'_next, E'stepE'_next⟩ => .inl <| .intro _ <| typeApp E'stepE'_next
    | .inr ⟨VE', VE'eqE'⟩ => by
      have E'val := VE'.property
      rw [VE'eqE'] at E'val
      let .typeGen E'' := E'
      exact .inl <| .intro _ typeGenApp

end OperationalSemantics

filter "LottExamples/SystemF/main.tex" "LottExamples/SystemF/main.mng"

end LottExamples.SystemF
