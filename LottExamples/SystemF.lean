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

theorem Type'.TypeVarLocallyClosed.TypeVar_open_eq {A : Type'}
  (h : A.TypeVarLocallyClosed m) (mlen : m ≤ n)
  : A.TypeVar_open x n = A := by match A, h with
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

theorem Type'.TypeVarLocallyClosed.Type'_open_eq {A : Type'}
  (h : A.TypeVarLocallyClosed m) (mlen : m ≤ n)
  : A.Type'_open B n = A := by match A, h with
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

theorem Type'.TypeVar_open_Type'_open_eq {A B : Type'}
  (Blc : B.TypeVarLocallyClosed m) (mnen : m ≠ n)
  : (A.TypeVar_open a m).Type'_open B n =
    (A.Type'_open B n).TypeVar_open a m := by
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

theorem Type'.TypeVar_open_Type'_open_eq' {A B : Type'}
  (Blc : B.TypeVarLocallyClosed n)
  : (A.TypeVar_open a n).Type'_open B n =
    A.TypeVar_open a n := by
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

theorem Term.TermVar_open_Term_open_eq {E F : Term}
  (Flc : F.TermVarLocallyClosed m) (mnen : m ≠ n)
  : (E.TermVar_open x m).Term_open F n =
    (E.Term_open F n).TermVar_open x m := by
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
  : (E.TermVar_open x m).TypeVar_open a n =
    (E.TypeVar_open a n).TermVar_open x m := by match E with
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

theorem Term.TypeVar_open_Type'_open_eq {E : Term} {A : Type'}
  (Alc : A.TypeVarLocallyClosed m) (mnen : m ≠ n)
  : (E.TypeVar_open a m).Type'_open A n =
    (E.Type'_open A n).TypeVar_open a m := by
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

theorem Term.TypeVar_open_Term_open_eq {E F : Term}
  (Flc : F.TypeVarLocallyClosed n)
  : (E.TypeVar_open x n).Term_open F m = (E.Term_open F m).TypeVar_open x n :=
  by match E with
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

nosubst
nonterminal Environment, G, D :=
  | "ε"                  : empty
  | G ", " x " : " A     : termVarExt (id x)
  | G ", " a             : typeVarExt (id a)
  | G ", " D             : append
    (elab := return mkAppN (.const `LottExamples.SystemF.Environment.append []) #[G, D])
  | "(" G ")"            : paren (desugar := return G)
  | G "^" a              : typeVarOpen (id a)
    (elab := return mkAppN (.const `LottExamples.SystemF.Environment.TypeVar_open [])
               #[G, a, .const `Nat.zero [] ])
  | G "^^" A             : typeOpen
    (elab := return mkAppN (.const `LottExamples.SystemF.Environment.Type'_open [])
               #[G, A, .const `Nat.zero [] ])

namespace Environment

def append (G : Environment) : Environment → Environment
  | empty => G
  | termVarExt G' x A => G.append G' |>.termVarExt x A
  | typeVarExt G' a => G.append G' |>.typeVarExt a

theorem append_termVarExt : [[(G, G', x : A)]] = [[((G, G'), x : A)]] := rfl

theorem append_typeVarExt : [[(G, G', a)]] = [[((G, G'), a)]] := rfl

theorem empty_append (G : Environment) : empty.append G = G :=
  match G with
  | empty => rfl
  | termVarExt G' x A => by rw [append_termVarExt, empty_append G']
  | typeVarExt G' a => by rw [append_typeVarExt, empty_append G']

theorem append_assoc : [[(G, G', G'')]] = [[((G, G'), G'')]] := match G'' with
  | empty => rfl
  | termVarExt G''' x A => by
    rw [append_termVarExt, append_termVarExt, G.append_assoc, append_termVarExt]
  | typeVarExt G''' a => by
    rw [append_typeVarExt, append_typeVarExt, G.append_assoc, append_typeVarExt]

def Type'_open (G : Environment) (A : Type') (n : Nat) : Environment :=
  match G, n with
  | empty, _ => empty
  | termVarExt G' x A', _ => G'.Type'_open A n |>.termVarExt x <| A'.Type'_open A n
  | G@(typeVarExt ..), 0 => G
  | typeVarExt G' a, n' + 1 => G'.Type'_open A n' |>.typeVarExt a

def TypeVar_open (G : Environment) (a : TypeVarId) (n : Nat) : Environment :=
  match G, n with
  | empty, _ => empty
  | termVarExt G' x A', _ => G'.TypeVar_open a n |>.termVarExt x <| A'.TypeVar_open a n
  | G@(typeVarExt ..), 0 => G
  | typeVarExt G' a', n' + 1 => G'.TypeVar_open a n' |>.typeVarExt a'

def termVar_count : Environment → Nat
  | empty => 0
  | termVarExt G _ _ => 1 + G.termVar_count
  | typeVarExt G _ => G.termVar_count

def typeVar_count : Environment → Nat
  | empty => 0
  | termVarExt G _ _ => G.typeVar_count
  | typeVarExt G _ => 1 + G.typeVar_count

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

theorem Type'_open {G : Environment}
  : TypeVarInEnvironment a (G.TypeVar_open a' n) →
    TypeVarInEnvironment a (G.Type'_open B n) := fun ainG => by
  match G, n with
  | .termVarExt .., _ =>
    rw [Environment.Type'_open]
    let .termVarExt ainG' := ainG
    exact termVarExt ainG'.Type'_open
  | .typeVarExt .., 0 =>
    rw [Environment.Type'_open]
    exact ainG
  | .typeVarExt G' a', n' + 1 =>
    rw [Environment.Type'_open]
    match ainG with
    | head => exact head
    | typeVarExt ainG' anea' => exact typeVarExt ainG'.Type'_open anea'

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

theorem append_inl (xAinG : [[x : A ∈ G]]) (xninGG : [[x ∉ GG]])
  : [[x : A ∈ G, GG]] := by
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

theorem Type'_open {A : Type'} {G : Environment}
  : TermVarInEnvironment x (A.TypeVar_open a n) (G.TypeVar_open a n) →
    TermVarInEnvironment x (A.Type'_open B n) (G.Type'_open B n) := sorry

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

theorem exists_gt (A : Type') : ∃ a : Nat, ∀ a' : Nat, [[a' ∈ ftv(A)]] → a' < a :=
  match A with
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

theorem arr : [[a ∉ ftv(A → B)]] ↔ [[a ∉ ftv(A)]] ∧ [[a ∉ ftv(B)]] := ⟨
    fun anin => ⟨(anin <| .arrl ·), (anin <| .arrr ·)⟩,
    fun
      | ⟨aninA, _⟩, .arrl ainA => aninA ainA
      | ⟨_, aninB⟩, .arrr ainB => aninB ainB
  ⟩

theorem forall' : [[a ∉ ftv(∀ b. A)]] → [[a ∉ ftv(A)]] := (· <| .forall' ·)

theorem TypeVar_open_of_ne (h : a ≠ a') : [[a ∉ ftv(A)]] → [[a ∉ ftv(A^a')]] :=
  (· <| ·.of_TypeVar_open h)

theorem TypeVar_open_inj_of {A B : Type'} (aninftvA : [[a ∉ ftv(A)]]) (aninftvB : [[a ∉ ftv(B)]])
  : A.TypeVar_open a n = B.TypeVar_open a n → A = B := by
  intro AopeqBop
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

end NotInTypeFreeTypeVars

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

theorem exists_gt (E : Term) : ∃ x : Nat, ∀ x' : Nat, [[x' ∈ fv(E)]] → x' < x :=
  match E with
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

theorem exists_gt (E : Term) : ∃ a : Nat, ∀ a' : Nat, [[a' ∈ ftv(E)]] → a' < a :=
  match E with
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

theorem TermVar_drop (Bwf : [[G, x : A, G' ⊢ B]]) : [[G, G' ⊢ B]] :=
  match B, Bwf with
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

theorem TypeVarLocallyClosed_of : [[G ⊢ A]] → A.TypeVarLocallyClosed G.typeVar_count :=
  fun Awf =>
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

theorem Type'_open_preservation {A : Type'} {G : Environment} (aninftvA : [[a ∉ ftv(A)]]) (Bwf : [[ε ⊢ B]])
  : TypeWellFormedness ((Environment.empty.typeVarExt a).append (G.TypeVar_open a n))
    (A.TypeVar_open a n) →
    TypeWellFormedness (G.Type'_open B n) (A.Type'_open B n) := fun Aopwf => by
  match A with
  | .var (.free a') =>
    rw [Type'.TypeVar_open, if_neg (nomatch ·)] at Aopwf
    let .var a'inaG := Aopwf
    match a'inaG.append_elim with
    | .inl .head => exact aninftvA .var |>.elim
    | .inr a'inG => exact .var a'inG.Type'_open
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
      have Gopeq : (G.TypeVar_open a n).typeVarExt a' = (G.typeVarExt a').TypeVar_open a (n + 1) :=
        by rw [Environment.TypeVar_open]
      rw [← A'.TypeVar_open_Type'_open_eq Bwf.TypeVarLocallyClosed_of_empty (Nat.zero_ne_add_one _)]
      rw [A'.TypeVar_open_comm a'nea.symm (Nat.succ_ne_zero _), ← Environment.append_typeVarExt,
          Gopeq] at this
      exact Type'_open_preservation (aninftvA.forall'.TypeVar_open_of_ne a'nea.symm) Bwf this

end TypeWellFormedness

judgement_syntax G " ⊢ " E " : " A : Typing

judgement Typing :=

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
    | _, .var _ => .var_free
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
    | _, .var _ => .var
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

theorem weakening (EtyA : [[G ⊢ E : A]]) : [[G', G ⊢ E : A]] := by
  induction EtyA with
  | var xin => exact .var xin.append_inr
  | lam Awf _ ih => exact .lam Awf.weakening ih
  | app _ _ ihE ihF => exact .app ihE ihF
  | typeGen _ ih => exact .typeGen ih
  | typeApp _ Bwf ih => exact .typeApp ih Bwf.weakening

theorem Term_open_preservation {E : Term}
  (EtyB : Typing ((Environment.empty.termVarExt x A).append G) (E.TermVar_open x n) B)
  (xninG : [[x ∉ G]]) (xninfvE : [[x ∉ fv(E)]]) (FtyA : [[ε ⊢ F : A]])
  : Typing G (E.Term_open F n) B := by
  match E with
  | .var (.free _) =>
    rw [Term.Term_open, if_neg (nomatch ·)]
    let .var x'BinεxAG := EtyB
    match x'BinεxAG.append_elim with
    | .inl ⟨.head, _⟩ => exact xninfvE .var |>.elim
    | .inr xBinG => exact var xBinG
  | .var (.bound _) =>
    rw [Term.Term_open]
    split
    · case isTrue h =>
      rw [← h, Term.TermVar_open, if_pos rfl] at EtyB
      let .var xBinxAG := EtyB
      match xBinxAG.append_elim with
      | .inl ⟨.head, _⟩ => exact FtyA.weakening
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
  (EtyA : Typing ((Environment.empty.typeVarExt a).append (G.TypeVar_open a n))
    (E.TypeVar_open a n) (A.TypeVar_open a n)) (aninG : [[a ∉ G]]) (aninftvE : [[a ∉ ftv(E)]])
  (aninftvA : [[a ∉ ftv(A)]]) (Bwf : [[ε ⊢ B]])
  : Typing (G.Type'_open B n) (E.Type'_open B n) (A.Type'_open B n) := by
  generalize E'eq : E.TypeVar_open a n = E', A'eq : A.TypeVar_open a n = A' at *
  match E, A, EtyA with
  | .var (.free x), A, .var xAopinεaG =>
    rw [Term.Type'_open]
    cases E'eq
    cases A'eq
    let .inr xAopinG := xAopinεaG.append_elim
    exact var xAopinG.Type'_open
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
        rw [← Environment.Type'_open, ← E''.TermVar_open_Type'_open_comm]
        rw [← Environment.append_termVarExt, ← Term.TermVar_open_TypeVar_open_eq] at this
        exact this.Type'_open_preservation aninG.termVarExt aninftvE.lam.right.TermVar_open
          (NotInTypeFreeTypeVars.arr.mp aninftvA).right Bwf
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
      have Gopeq : (G.TypeVar_open a n).typeVarExt a' = (G.typeVarExt a').TypeVar_open a (n + 1) :=
        by rw [Environment.TypeVar_open]
      rw [← Environment.append_typeVarExt, E'.TypeVar_open_comm a'nea.symm (Nat.succ_ne_zero _),
          A'.TypeVar_open_comm a'nea.symm (Nat.succ_ne_zero _), Gopeq] at this
      exact this.Type'_open_preservation (G := G.typeVarExt a')
        (aninG.typeVarExt a'nea.symm)
        (aninftvE.typeGen.TypeVar_open_of_ne a'nea.symm)
        (aninftvA.forall'.TypeVar_open_of_ne a'nea.symm) Bwf
  | .typeApp E' B', A, .typeApp E'ty B'wf (A := A') =>
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
