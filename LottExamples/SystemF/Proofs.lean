import Aesop
import LottExamples.SystemF.Semantics

namespace LottExamples.SystemF

namespace «Type»

@[simp]
theorem TypeVar_open_sizeOf : sizeOf (TypeVar_open A a n) = sizeOf A := by
  induction A generalizing n <;> aesop (add simp TypeVar_open)

theorem TypeVar_open_comm (A : «Type»)
  : m ≠ n → (A.TypeVar_open a m).TypeVar_open a' n = (A.TypeVar_open a' n).TypeVar_open a m := by
  induction A generalizing m n <;> aesop (add simp TypeVar_open)

namespace TypeVarLocallyClosed

theorem weakening (Alc : TypeVarLocallyClosed A m) : m ≤ n → A.TypeVarLocallyClosed n := by
  induction Alc generalizing n
  all_goals aesop (add safe constructors TypeVarLocallyClosed, 20% Nat.lt_of_lt_of_le)

theorem TypeVar_open_drop
  : m < n → (TypeVar_open A a m).TypeVarLocallyClosed n → A.TypeVarLocallyClosed n := by
  induction A generalizing m n <;> aesop
    (add simp TypeVar_open, safe cases TypeVarLocallyClosed, safe constructors TypeVarLocallyClosed)

theorem TypeVar_open_id : TypeVarLocallyClosed A n → A.TypeVar_open a n = A := by
  induction A generalizing n <;> aesop (add simp TypeVar_open, safe cases TypeVarLocallyClosed)

theorem Type_open_id : TypeVarLocallyClosed A n → A.Type_open B n = A := by
  induction A generalizing n <;> aesop (add simp Type_open, safe cases TypeVarLocallyClosed)

theorem TypeVar_open_TypeVar_close_id
  : TypeVarLocallyClosed A n → (A.TypeVar_close a n).TypeVar_open a n = A := by
  induction A generalizing n <;> aesop
    (add simp [TypeVar_open, TypeVar_close], safe cases TypeVarLocallyClosed)

theorem TypeVar_close_Type_open_eq_TypeVar_subst
  : TypeVarLocallyClosed A n → (A.TypeVar_close a n).Type_open B n = A.TypeVar_subst a B := by
  induction A generalizing n <;> aesop
    (add simp [TypeVar_close, Type_open, TypeVar_subst], safe cases TypeVarLocallyClosed)

theorem TypeVar_open_Type_open_comm : TypeVarLocallyClosed B m → m ≠ n →
    (TypeVar_open A a m).Type_open B n = (A.Type_open B n).TypeVar_open a m := by
  induction A generalizing m n <;> aesop
    (add simp [TypeVar_open, Type_open], 20% apply [((TypeVar_open_id · |>.symm)), weakening])

theorem TypeVar_subst_TypeVar_open_comm : TypeVarLocallyClosed B n → a ≠ a' →
    (TypeVar_subst A a B).TypeVar_open a' n = (A.TypeVar_open a' n).TypeVar_subst a B := by
  induction A generalizing n <;> aesop
    (add simp [TypeVar_open, TypeVar_subst], 20% apply [TypeVar_open_id, weakening])

end TypeVarLocallyClosed

end «Type»

namespace Term

@[simp]
theorem TermVar_open_sizeOf : sizeOf (TermVar_open E x n) = sizeOf E := by
  induction E generalizing n <;> aesop (add simp TermVar_open)

@[simp]
theorem TypeVar_open_sizeOf : sizeOf (TypeVar_open E x n) = sizeOf E := by
  induction E generalizing n <;> aesop (add simp TypeVar_open)

theorem TermVar_open_comm (E : Term)
  : m ≠ n → (E.TermVar_open x m).TermVar_open x' n = (E.TermVar_open x' n).TermVar_open x m := by
  induction E generalizing m n <;> aesop (add simp TermVar_open)

theorem TypeVar_open_comm (E : Term)
  : m ≠ n → (E.TypeVar_open a m).TypeVar_open a' n = (E.TypeVar_open a' n).TypeVar_open a m := by
  induction E generalizing m n <;> aesop (add simp TypeVar_open, safe apply Type.TypeVar_open_comm)

theorem TermVar_open_Type_open_comm (E : Term)
  : (E.TermVar_open x m).Type_open A n = (E.Type_open A n).TermVar_open x m := by
  induction E generalizing m n <;> aesop (add simp TermVar_open, simp Type_open)

theorem TermVar_open_TypeVar_open_comm (E : Term)
  : (E.TermVar_open x m).TypeVar_open a n = (E.TypeVar_open a n).TermVar_open x m := by
  induction E generalizing m n <;> aesop (add simp [TermVar_open, TypeVar_open])

namespace TermVarLocallyClosed

theorem weakening (Elc : TermVarLocallyClosed E m) : m ≤ n → E.TermVarLocallyClosed n := by
  induction Elc generalizing n
  all_goals aesop (add unsafe 20% constructors TermVarLocallyClosed, unsafe 20% Nat.lt_of_lt_of_le)

theorem TermVar_open_drop
  : m < n → (TermVar_open E x m).TermVarLocallyClosed n → E.TermVarLocallyClosed n := by
  induction E generalizing m n <;> aesop
    (add simp TermVar_open, safe cases TermVarLocallyClosed, safe constructors TermVarLocallyClosed)

theorem TypeVar_open_drop
  : (TypeVar_open E a m).TermVarLocallyClosed n → E.TermVarLocallyClosed n := by
  induction E generalizing m n <;> aesop
    (add simp TypeVar_open, safe cases TermVarLocallyClosed, safe constructors TermVarLocallyClosed)

theorem TermVar_open_id : TermVarLocallyClosed E n → E.TermVar_open x n = E := by
  induction E generalizing n <;> aesop (add simp TermVar_open, safe cases TermVarLocallyClosed)

theorem TermVar_open_Term_open_id
  : TermVarLocallyClosed F m → m ≠ n →
    (TermVar_open E x m).Term_open F n = (E.Term_open F n).TermVar_open x m := by
  induction E generalizing m n <;> aesop
    (add simp [TermVar_open, Term_open], 20% apply [((TermVar_open_id · |>.symm)), weakening])

end TermVarLocallyClosed

namespace TypeVarLocallyClosed

theorem weakening (Elc : TypeVarLocallyClosed E m) : m ≤ n → E.TypeVarLocallyClosed n := by
  induction Elc generalizing n <;> aesop
    (add safe constructors TypeVarLocallyClosed, 20% apply Type.TypeVarLocallyClosed.weakening)

theorem TermVar_open_drop
  : (TermVar_open E x m).TypeVarLocallyClosed n → E.TypeVarLocallyClosed n := by
  induction E generalizing m n <;> aesop
    (add simp TermVar_open, safe cases TypeVarLocallyClosed, safe constructors TypeVarLocallyClosed)

theorem TypeVar_open_drop
  : m < n → (TypeVar_open E a m).TypeVarLocallyClosed n → E.TypeVarLocallyClosed n := by
  induction E generalizing m n <;> aesop
    (add simp TypeVar_open, safe cases TypeVarLocallyClosed, safe constructors TypeVarLocallyClosed,
      20% apply [Type.TypeVarLocallyClosed.TypeVar_open_drop])

theorem TypeVar_open_id (Elc : TypeVarLocallyClosed E n) : E.TypeVar_open x n = E := by
  induction Elc <;> aesop
    (add simp TypeVar_open, 20% apply [Type.TypeVarLocallyClosed.TypeVar_open_id])

theorem TypeVar_open_Term_open_comm : TypeVarLocallyClosed F n →
    (TypeVar_open E x n).Term_open F m = (E.Term_open F m).TypeVar_open x n := by
  induction E generalizing m n <;> aesop
    (add simp [TypeVar_open, Term_open], 20% apply [((TypeVar_open_id · |>.symm)), weakening])

end TypeVarLocallyClosed

theorem TypeVar_open_Type_open_comm (E : Term) : Type.TypeVarLocallyClosed A m → m ≠ n →
    (TypeVar_open E a m).Type_open A n = (E.Type_open A n).TypeVar_open a m := by
  induction E generalizing m n <;> aesop
    (add simp [TypeVar_open, Type_open],
      20% apply [Type.TypeVarLocallyClosed.TypeVar_open_Type_open_comm,
                 Type.TypeVarLocallyClosed.weakening])

end Term

namespace Environment

theorem append_termVarExt : [[Γ, (Γ', x : A)]] = [[(Γ, Γ'), x : A]] := rfl

theorem append_typeVarExt : [[Γ, (Γ', a)]] = [[(Γ, Γ'), a]] := rfl

theorem empty_append (Γ : Environment) : empty.append Γ = Γ := match Γ with
  | [[ε]] => rfl
  | [[Γ', x : A]] => by rw [append_termVarExt, empty_append Γ']
  | [[Γ', a]] => by rw [append_typeVarExt, empty_append Γ']

theorem append_empty (Γ : Environment) : Γ.append empty = Γ := by match Γ with
  | [[ε]] => rfl
  | [[Γ', x : A]] => rw [append]
  | [[Γ', a]] => rw [append]

theorem append_assoc : [[Γ, (Γ', Γ'')]] = [[(Γ, Γ'), Γ'']] := match Γ'' with
  | [[ε]] => rfl
  | [[Γ''', x : A]] => by
    rw [append_termVarExt, append_termVarExt, Γ.append_assoc, append_termVarExt]
  | [[Γ''', a]] => by
    rw [append_typeVarExt, append_typeVarExt, Γ.append_assoc, append_typeVarExt]

theorem termVar_domain_append
  : [[Γ, Γ']].termVar_domain = Γ'.termVar_domain ++ Γ.termVar_domain := by match Γ' with
  | [[ε]] => rw [termVar_domain, append_empty, List.nil_append]
  | [[Γ'', x : A]] =>
    rw [append_termVarExt, termVar_domain, termVar_domain, termVar_domain_append, List.cons_append]
  | [[Γ'', a]] =>
    rw [append_typeVarExt, termVar_domain, termVar_domain, termVar_domain_append]

theorem typeVar_domain_append
  : [[Γ, Γ']].typeVar_domain = Γ'.typeVar_domain ++ Γ.typeVar_domain := by match Γ' with
  | [[ε]] => rw [typeVar_domain, append_empty, List.nil_append]
  | [[Γ'', x : A]] =>
    rw [append_termVarExt, typeVar_domain, typeVar_domain, typeVar_domain_append]
  | [[Γ'', a]] =>
    rw [append_typeVarExt, typeVar_domain, typeVar_domain, typeVar_domain_append, List.cons_append]

end Environment

namespace TypeVarInEnvironment

theorem append_elim (ainΓappΓ' : [[a ∈ Γ, Γ']]) : [[a ∈ Γ]] ∨ [[a ∈ Γ']] := by
  by_cases [[a ∈ Γ']]
  · case pos ainΓ' => exact .inr ainΓ'
  · case neg aninΓ' =>
    left
    induction Γ'
    · case empty => exact ainΓappΓ'
    · case termVarExt Γ'' x A ih =>
      apply ih
      · cases ainΓappΓ'
        case ainΓappΓ'.termVarExt => assumption
      · intro ainΓ''
        exact aninΓ' ainΓ''.termVarExt
    · case typeVarExt GG' a' ih =>
      by_cases a' = a
      · case pos a'eqa =>
        apply False.elim
        apply aninΓ'
        rw [a'eqa]
        exact head
      · case neg a'nea =>
        apply ih
        · cases ainΓappΓ'
          · case ainΓappΓ'.head => contradiction
          · case ainΓappΓ'.typeVarExt => assumption
        · intro ainΓ''
          apply aninΓ'
          have a'nea : a' ≠ a := a'nea
          exact ainΓ''.typeVarExt a'nea.symm

theorem append_inl (ainΓ : [[a ∈ Γ]]) : [[a ∈ Γ, Γ']] := by
  match Γ' with
  | [[ε]] => exact ainΓ
  | [[Γ'', x : A]] => exact ainΓ.append_inl |>.termVarExt
  | [[Γ'', a']] =>
    by_cases a' = a
    · case pos a'eqa =>
      rw [a'eqa]
      exact .head
    · case neg a'nea =>
      have a'nea : a' ≠ a := a'nea
      exact .typeVarExt ainΓ.append_inl a'nea.symm

theorem append_inr : [[a ∈ Γ']] → [[a ∈ Γ, Γ']]
  | head => head
  | termVarExt ainΓ'' => ainΓ''.append_inr |>.termVarExt
  | typeVarExt ainΓ'' anea' => ainΓ''.append_inr |>.typeVarExt anea'

theorem TypeVar_subst : [[a ∈ Γ]] → [[a ∈ Γ [A / a'] ]]
  | termVarExt ainΓ' => by
    rw [Environment.TypeVar_subst]
    exact termVarExt <| ainΓ'.TypeVar_subst
  | typeVarExt ainΓ' anea'' => by
    rw [Environment.TypeVar_subst]
    exact typeVarExt (ainΓ'.TypeVar_subst) anea''
  | head => by
    rw [Environment.TypeVar_subst]
    exact head

end TypeVarInEnvironment

namespace TypeVarNotInEnvironment

theorem termVarExt : [[a ∉ Γ]] → [[a ∉ Γ, x : A]]
  | aninΓ, .termVarExt ainΓ => aninΓ ainΓ

theorem typeVarExt (h : a ≠ a') : [[a ∉ Γ]] → [[a ∉ Γ, a']]
  | _, .head => h rfl
  | aninΓ, .typeVarExt ainΓ _ => aninΓ ainΓ

end TypeVarNotInEnvironment

namespace TermVarInEnvironment

theorem append_elim (xAinΓappΓ' : [[x : A ∈ Γ, Γ']])
  : [[x : A ∈ Γ]] ∧ [[x ∉ Γ']] ∨ [[x : A ∈ Γ']] := by
  by_cases [[x : A ∈ Γ']]
  · case pos xAinΓ' => exact .inr xAinΓ'
  · case neg xAninΓ' =>
    left
    match Γ' with
    | [[ε]] =>
      constructor
      · exact xAinΓappΓ'
      · intro A'
        intro xA'inε
        nomatch xA'inε
    | [[Γ'', x' : A']] =>
      by_cases x' = x
      · case pos x'eqx =>
        by_cases A' = A
        · case pos A'eqA =>
          rw [x'eqx, A'eqA] at xAinΓappΓ' xAninΓ'
          exact xAninΓ' head |>.elim
        · case neg A'neA =>
          cases xAinΓappΓ'
          · case head => contradiction
          · case termVarExt xAinΓappΓ'' xnex' =>
            exact xnex' x'eqx.symm |>.elim
      · case neg x'nex =>
        cases xAinΓappΓ'
        · case head => contradiction
        · case termVarExt xAinΓappΓ'' xnex' =>
          rcases xAinΓappΓ''.append_elim with ⟨xAinΓ, xninΓ''⟩ | xAinΓ''
          · constructor
            · exact xAinΓ
            · intro A''
              intro xA''inΓ''x'A'
              match xA''inΓ''x'A' with
              | head => contradiction
              | termVarExt xA''inΓ'  _ => exact xninΓ'' A'' xA''inΓ'
          · have x'nex : x' ≠ x := x'nex
            exact False.elim <| xAninΓ' <| xAinΓ''.termVarExt x'nex.symm
    | [[Γ'', a]] =>
      cases xAinΓappΓ'
      case typeVarExt xAinΓappΓ'' =>
      match xAinΓappΓ''.append_elim with
      | .inl ⟨xAinΓ, xninΓ''⟩ =>
        constructor
        · exact xAinΓ
        · intro A' xA'inΓ''a
          apply xninΓ'' A'
          cases xA'inΓ''a
          case right.typeVarExt xA'inΓ'' =>
          exact xA'inΓ''
      | .inr xAinΓ'' =>
        exact xAninΓ' xAinΓ''.typeVarExt |>.elim

theorem append_inr : [[x : A ∈ Γ']] → [[x : A ∈ Γ, Γ']]
  | head => head
  | termVarExt xAinΓ'' xnex' => xAinΓ''.append_inr |>.termVarExt xnex'
  | typeVarExt xAinΓ'' => xAinΓ''.append_inr |>.typeVarExt

end TermVarInEnvironment

namespace TermVarNotInEnvironment

theorem termVarExt (xnex' : x ≠ x') : [[x ∉ Γ]] → [[x ∉ Γ, x' : A]] := fun xnin A xAinΓx'A => by
  apply xnin A
  cases xAinΓx'A
  · case head => contradiction
  · case termVarExt h _ => exact h

theorem typeVarExt : [[x ∉ Γ]] → [[x ∉ Γ, a]] := fun xnin A xAinΓa => by
  apply xnin A
  cases xAinΓa
  case typeVarExt h =>
  exact h

end TermVarNotInEnvironment

namespace Type.InFreeTypeVars

theorem of_TypeVar_open {A : «Type»} (h : a ≠ a')
  : InFreeTypeVars a (A.TypeVar_open a' n) → [[a ∈ ftv(A)]] := fun ainAop => by
  match A with
  | .var (.free _) => rwa [Type.TypeVar_open] at ainAop
  | .var (.bound _) =>
    rw [Type.TypeVar_open] at ainAop
    split at ainAop
    · case isTrue h =>
      cases List.mem_singleton.mp ainAop
      nomatch h
    · case isFalse h => nomatch ainAop
  | [[A' → B]] =>
    rw [Type.TypeVar_open] at ainAop
    exact List.mem_append.mpr <| match List.mem_append.mp ainAop with
    | .inl ainA'op => .inl <| of_TypeVar_open h ainA'op
    | .inr ainA'op => .inr <| of_TypeVar_open h ainA'op
  | [[∀ a. A']] =>
    rw [Type.TypeVar_open] at ainAop
    rw [InFreeTypeVars, freeTypeVars] at ainAop ⊢
    exact of_TypeVar_open h ainAop

end Type.InFreeTypeVars

namespace Type.NotInFreeTypeVars

theorem arr : [[a ∉ ftv(A → B)]] ↔ [[a ∉ ftv(A)]] ∧ [[a ∉ ftv(B)]] where
  mp anin := ⟨(anin <| List.mem_append.mpr <| .inl ·), (anin <| List.mem_append.mpr <| .inr ·)⟩
  mpr | ⟨aninA, aninB⟩, ainAarrB => match List.mem_append.mp ainAarrB with
    | .inl ainA => aninA ainA
    | .inr ainB => aninB ainB

theorem «forall» : [[a ∉ ftv(∀ a'. A)]] → [[a ∉ ftv(A)]] := (· ·)

theorem TypeVar_open_of_ne (h : a ≠ a') : [[a ∉ ftv(A)]] → [[a ∉ ftv(A^a')]] :=
  (· <| ·.of_TypeVar_open h)

theorem TypeVar_open_inj_of {A B : «Type»} (aninftvA : [[a ∉ ftv(A)]]) (aninftvB : [[a ∉ ftv(B)]])
  : A.TypeVar_open a n = B.TypeVar_open a n → A = B := fun AopeqBop => by
  match A, B with
  | .var (.free _), .var (.free _) =>
    rw [Type.TypeVar_open, if_neg nofun, Type.TypeVar_open, if_neg nofun] at AopeqBop
    exact AopeqBop
  | .var (.free _), .var (.bound _) =>
    rw [Type.TypeVar_open, if_neg nofun, Type.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [Type.var.inj AopeqBop] at aninftvA
      nomatch List.not_mem_singleton.mp aninftvA
    · case isFalse h => nomatch AopeqBop
  | .var (.bound _), .var (.free _) =>
    rw [Type.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [Type.TypeVar_open, if_neg nofun] at AopeqBop
      rw [← Type.var.inj AopeqBop] at aninftvB
      nomatch List.not_mem_singleton.mp aninftvB
    · case isFalse h => nomatch AopeqBop
  | .var (.bound _), .var (.bound _) =>
    rw [Type.TypeVar_open] at AopeqBop
    split at AopeqBop
    · case isTrue h =>
      rw [← h]
      rw [Type.TypeVar_open] at AopeqBop
      split at AopeqBop
      · case isTrue h' => rw [← h']
      · case isFalse h' => nomatch AopeqBop
    · case isFalse h =>
      rw [Type.TypeVar_open] at AopeqBop
      split at AopeqBop
      · case isTrue h' => nomatch AopeqBop
      · case isFalse h' => exact AopeqBop
  | [[A' → B']], [[A'' → B'']] =>
    rw [Type.TypeVar_open, Type.TypeVar_open] at AopeqBop
    let ⟨A'opeqA''op, B'opeqB''op⟩ := Type.arr.inj AopeqBop
    rw [(arr.mp aninftvA).left.TypeVar_open_inj_of (arr.mp aninftvB).left A'opeqA''op,
        (arr.mp aninftvA).right.TypeVar_open_inj_of (arr.mp aninftvB).right B'opeqB''op]
  | [[∀ a. A']], [[∀ a. A'']] =>
    rw [Type.TypeVar_open, Type.TypeVar_open] at AopeqBop
    rw [aninftvA.forall.TypeVar_open_inj_of aninftvB.forall <| Type.forall.inj AopeqBop]

theorem TypeVar_open_TypeVar_subst_eq_Type_open_of
  : [[a ∉ ftv(A)]] → (A.TypeVar_open a n).TypeVar_subst a B = A.Type_open B n := fun aninftvA => by
  match A with
  | .var (.free _) =>
    rw [Type.TypeVar_open, if_neg nofun, Type.TypeVar_subst]
    split
    · case isTrue h =>
      rw [← h] at aninftvA
      nomatch List.not_mem_singleton.mp aninftvA
    · case isFalse h => rw [Type.Type_open, if_neg nofun]
  | .var (.bound _) =>
    rw [Type.TypeVar_open]
    split
    · case isTrue h => rw [Type.TypeVar_subst, if_pos rfl, Type.Type_open, if_pos h]
    · case isFalse h => rw [Type.TypeVar_subst, if_neg nofun, Type.Type_open, if_neg h]
  | [[A' → B']] =>
    rw [Type.TypeVar_open, Type.TypeVar_subst,
        arr.mp aninftvA |>.left.TypeVar_open_TypeVar_subst_eq_Type_open_of,
        arr.mp aninftvA |>.right.TypeVar_open_TypeVar_subst_eq_Type_open_of, ← Type.Type_open]
  | [[∀ a. A']] =>
    rw [Type.TypeVar_open, Type.TypeVar_subst,
        aninftvA.forall.TypeVar_open_TypeVar_subst_eq_Type_open_of, ← Type.Type_open]

theorem TypeVar_close_eq_of {A : «Type»} : [[a ∉ ftv(A)]] → A.TypeVar_close a n = A :=
  fun aninftvA => by match A with
  | .var (.free _) =>
    rw [Type.TypeVar_close]
    split
    · case isTrue h =>
      rw [← h] at aninftvA
      nomatch List.not_mem_singleton.mp aninftvA
    · case isFalse h => rfl
  | .var (.bound _) => rw [Type.TypeVar_close, if_neg nofun]
  | [[A' → B]] =>
    rw [Type.TypeVar_close, arr.mp aninftvA |>.left.TypeVar_close_eq_of,
        arr.mp aninftvA |>.right.TypeVar_close_eq_of]
  | [[∀ a. A']] => rw [Type.TypeVar_close, aninftvA.forall.TypeVar_close_eq_of]

theorem TypeVar_close_TypeVar_open_of {A : «Type»}
  : [[a ∉ ftv(A)]] → (A.TypeVar_open a n).TypeVar_close a n = A := fun aninftvA => by match A with
  | .var (.free _) => rw [Type.TypeVar_open, if_neg nofun, aninftvA.TypeVar_close_eq_of]
  | .var (.bound _) =>
    rw [Type.TypeVar_open]
    split
    · case isTrue h => rw [Type.TypeVar_close, if_pos rfl, h]
    · case isFalse h => rw [Type.TypeVar_close, if_neg nofun]
  | [[A' → B]] =>
    rw [Type.TypeVar_open, Type.TypeVar_close,
        arr.mp aninftvA |>.left.TypeVar_close_TypeVar_open_of,
        arr.mp aninftvA |>.right.TypeVar_close_TypeVar_open_of]
  | [[∀ a. A']] =>
    rw [Type.TypeVar_open, Type.TypeVar_close, aninftvA.forall.TypeVar_close_TypeVar_open_of]

theorem of_TypeVar_close {A : «Type»} : NotInFreeTypeVars a (A.TypeVar_close a n) := by
  match A with
  | .var (.free _) =>
    rw [Type.TypeVar_close]
    split
    · case isTrue h => nofun
    · case isFalse h =>
      intro ain
      rw [List.mem_singleton.mp ain] at h
      nomatch h
  | .var (.bound _) =>
    rw [Type.TypeVar_close, if_neg nofun]
    nofun
  | [[A' → B]] =>
    rw [Type.TypeVar_close]
    exact arr.mpr ⟨of_TypeVar_close, of_TypeVar_close⟩
  | [[∀ a. A']] =>
    rw [Type.TypeVar_close]
    intro ain
    rw [InFreeTypeVars, freeTypeVars] at ain
    exact of_TypeVar_close ain

end Type.NotInFreeTypeVars

theorem TermVarInEnvironment.TypeVar_subst {A : «Type»} (aninftvA : [[a ∉ ftv(A)]])
  : TermVarInEnvironment x (A.TypeVar_open a n) [[ε, a, Γ]] →
    TermVarInEnvironment x (A.Type_open B n) [[(Γ [B / a])]] := fun xAopinεaΓ =>
  match Γ, xAopinεaΓ with
  | [[ε]], xAopinεaΓ => nomatch xAopinεaΓ
  | .termVarExt .., head => by
    rw [Environment.TypeVar_subst, aninftvA.TypeVar_open_TypeVar_subst_eq_Type_open_of]
    exact head
  | [[Γ', x' : A']], termVarExt xAopinεaΓ' xnex' =>
    xAopinεaΓ'.TypeVar_subst aninftvA |>.termVarExt xnex'
  | [[Γ', a']], typeVarExt xAopinεaΓ' => xAopinεaΓ'.TypeVar_subst aninftvA |>.typeVarExt

namespace «Type»

theorem Type_open_eq_of_TypeVar_open_eq {A A' B : «Type»}
  (h : A.TypeVar_open a n = A'.TypeVar_open a m) (aninftvA : [[a ∉ ftv(A)]])
  (aninftvA' : [[a ∉ ftv(A')]]) (Blc : B.TypeVarLocallyClosed o)
  : A.Type_open B n = A'.Type_open B m := by match A, A' with
  | var (.free _), var (.free _) =>
    rw [TypeVar_open, if_neg nofun, TypeVar_open, if_neg nofun] at h
    cases h
    rw [Type_open, if_neg nofun, Type_open, if_neg nofun]
  | var (.bound _), var (.free _) =>
    rw [TypeVar_open] at h
    split at h
    · case isTrue h' =>
      cases h'
      rw [TypeVar_open, if_neg nofun] at h
      cases h
      rw [Type_open, if_pos rfl, Type_open, if_neg nofun]
      nomatch List.not_mem_singleton.mp aninftvA'
    · case isFalse h' =>
      rw [TypeVar_open, if_neg nofun] at h
      cases h
  | var (.free _), var (.bound _) =>
    rw [TypeVar_open, if_neg nofun, TypeVar_open] at h
    split at h
    · case isTrue h' =>
      cases h'
      cases h
      nomatch List.not_mem_singleton.mp aninftvA
    · case isFalse h' =>
      cases h
  | var (.bound _), var (.bound _) =>
    rw [TypeVar_open] at h
    split at h
    · case isTrue h' =>
      cases h'
      rw [TypeVar_open] at h
      split at h
      · case isTrue h'' =>
        cases h''
        cases h
        rw [Type_open, if_pos rfl, Type_open, if_pos rfl]
      · case isFalse h'' =>
        cases h
    · case isFalse h' =>
      rw [TypeVar_open] at h
      split at h
      · case isTrue h'' =>
        cases h''
        nomatch h
      · case isFalse h'' =>
        cases h
        rw [Type_open, if_neg h', Type_open, if_neg h'']
  | [[A'' → B'']], [[A''' → B''']] =>
    rw [TypeVar_open, TypeVar_open] at h
    let ⟨h', h''⟩ := arr.inj h
    let ⟨aninftvA'', aninftvB''⟩ := NotInFreeTypeVars.arr.mp aninftvA
    let ⟨aninftvA''', aninftvB'''⟩ := NotInFreeTypeVars.arr.mp aninftvA'
    rw [Type_open, Type_open,
        Type_open_eq_of_TypeVar_open_eq h' aninftvA'' aninftvA''' Blc,
        Type_open_eq_of_TypeVar_open_eq h'' aninftvB'' aninftvB''' Blc]
  | [[∀ a. A'']], [[∀ a. A''']] =>
    rw [TypeVar_open, TypeVar_open] at h
    rw [Type_open, Type_open, Type_open_eq_of_TypeVar_open_eq (forall.inj h) aninftvA.forall
          aninftvA'.forall Blc]

theorem Type_open_TypeVar_subst_eq_of_TypeVar_open_eq {A A' B B' : «Type»}
  (h : A.TypeVar_open a n = A'.Type_open (B'.TypeVar_open a l) o) (Blc : B.TypeVarLocallyClosed o)
  (aninftvA : [[a ∉ ftv(A)]]) (aninftvB' : [[a ∉ ftv(B')]])
  : A.Type_open B n = (A'.TypeVar_subst a B).Type_open (B'.Type_open B l) o := by
  match A, A' with
  | var (.free _), var (.free _) =>
    rw [TypeVar_open, if_neg nofun, Type_open, if_neg nofun] at h
    cases h
    rw [Type_open, if_neg nofun, TypeVar_subst]
    split
    · case isTrue h' =>
      cases h'
      nomatch List.not_mem_singleton.mp aninftvA
    · case isFalse h' => rw [Type_open, if_neg nofun]
  | var (.bound _), var (.free _) =>
    rw [TypeVar_open] at h
    split at h
    · case isTrue h' =>
      cases h'
      rw [Type_open, if_neg nofun] at h
      cases h
      rw [Type_open, if_pos rfl, TypeVar_subst, if_pos rfl, Blc.Type_open_id]
    · case isFalse h' =>
      rw [Type_open, if_neg nofun] at h
      cases h
  | var (.free _), var (.bound _) =>
    rw [TypeVar_open, if_neg nofun, Type_open] at h
    split at h
    · case isTrue h' =>
      cases h'
      rw [Type_open, if_neg nofun, TypeVar_subst, if_neg nofun, Type_open, if_pos rfl]
      match B' with
      | var (.free _) =>
        rw [TypeVar_open, if_neg nofun] at h
        cases h
        rw [Type_open, if_neg nofun]
      | var (.bound _) =>
        rw [TypeVar_open] at h
        split at h
        · case isTrue h' =>
          cases h'
          cases h
          nomatch List.not_mem_singleton.mp aninftvA
        · case isFalse h' => nomatch h
    · case isFalse h' => nomatch h
  | var (.bound _), var (.bound _) =>
    rw [TypeVar_open] at h
    split at h
    · case isTrue h' =>
      cases h'
      rw [Type_open] at h
      split at h
      · case isTrue h' =>
        cases h'
        rw [Type_open, if_pos rfl, TypeVar_subst, if_neg nofun, Type_open, if_pos rfl]
        match B' with
        | var (.free _) =>
          rw [TypeVar_open, if_neg nofun] at h
          cases h
          nomatch List.not_mem_singleton.mp aninftvB'
        | var (.bound _) =>
          rw [TypeVar_open] at h
          split at h
          · case isTrue h' =>
            cases h'
            cases h
            rw [Type_open, if_pos rfl]
          · case isFalse h' => nomatch h
      · case isFalse h' => nomatch h
    · case isFalse h' =>
      rw [Type_open] at h
      split at h
      · case isTrue h'' =>
        cases h''
        rw [Type_open, if_neg h', TypeVar_subst, if_neg nofun, Type_open, if_pos rfl]
        match B' with
        | var (.free _) =>
          rw [TypeVar_open, if_neg nofun] at h
          exact h
        | var (.bound _) =>
          rw [TypeVar_open] at h
          split at h
          · case isTrue h'' =>
            cases h''
            cases h
          · case isFalse h'' =>
            cases h
            rw [Type_open, if_neg h'']
      · case isFalse h'' =>
        cases h
        rw [Type_open, if_neg h', TypeVar_subst, if_neg nofun, Type_open, if_neg h'']
  | [[A'' → B'']], [[A''' → B''']] =>
    rw [TypeVar_open, Type_open] at h
    let ⟨h', h''⟩ := arr.inj h
    let ⟨A''nin, B''nin⟩ := NotInFreeTypeVars.arr.mp aninftvA
    rw [Type_open, Type_open_TypeVar_subst_eq_of_TypeVar_open_eq h' Blc A''nin aninftvB',
        Type_open_TypeVar_subst_eq_of_TypeVar_open_eq h'' Blc B''nin aninftvB', TypeVar_subst,
        Type_open]
  | [[∀ a. A'']], [[∀ a. A''']] =>
    rw [TypeVar_open, Type_open] at h
    rw [Type_open, Type_open_TypeVar_subst_eq_of_TypeVar_open_eq (forall.inj h)
          (Blc.weakening (Nat.le_add_right ..)) aninftvA.forall aninftvB', TypeVar_subst,
          Type_open]
  | [[A'' → B'']], var (.bound _) =>
    rw [TypeVar_open, Type_open] at h
    split at h
    · case isTrue h' =>
      cases h'
      let [[A''' → B''']] := B'
      rw [← TypeVar_open] at h
      rw [TypeVar_subst, if_neg nofun, Type_open, if_pos rfl]
      exact Type_open_eq_of_TypeVar_open_eq h aninftvA aninftvB' Blc
    · case isFalse h' => nomatch h
  | [[∀ a. A'']], var (.bound _) =>
    rw [TypeVar_open, Type_open] at h
    split at h
    · case isTrue h' =>
      cases h'
      let [[∀ a. A''']] := B'
      rw [← TypeVar_open] at h
      rw [TypeVar_subst, if_neg nofun, Type_open, if_pos rfl]
      exact Type_open_eq_of_TypeVar_open_eq h aninftvA aninftvB' Blc
    · case isFalse h' => nomatch h

end «Type»

namespace Term.InFreeTermVars

theorem of_TermVar_open {E : Term} (h : x ≠ x')
  : InFreeTermVars x (E.TermVar_open x' n) → [[x ∈ fv(E)]] := fun xinEop => by
  match E with
  | .var (.free _) => rwa [Term.TermVar_open] at xinEop
  | .var (.bound _) =>
    rw [Term.TermVar_open] at xinEop
    split at xinEop
    · case isTrue h =>
      cases List.mem_singleton.mp xinEop
      nomatch h
    · case isFalse h => nomatch xinEop
  | [[λ x : A. E']] =>
    rw [Term.TermVar_open] at xinEop
    rw [InFreeTermVars, freeTermVars] at xinEop ⊢
    exact of_TermVar_open h xinEop
  | [[E' F]] =>
    rw [Term.TermVar_open] at xinEop
    exact List.mem_append.mpr <| match List.mem_append.mp xinEop with
    | .inl xinE'op => .inl <| of_TermVar_open h xinE'op
    | .inr xinE'op => .inr <| of_TermVar_open h xinE'op
  | [[Λ a. E']] =>
    rw [Term.TermVar_open] at xinEop
    rw [InFreeTermVars, freeTermVars] at xinEop ⊢
    exact of_TermVar_open h xinEop
  | [[E' [A] ]] =>
    rw [Term.TermVar_open] at xinEop
    rw [InFreeTermVars, freeTermVars] at xinEop ⊢
    exact of_TermVar_open h xinEop

theorem of_TypeVar_open {E : Term}
  : InFreeTermVars x (E.TypeVar_open a n) → [[x ∈ fv(E)]] := fun xinEop => by
  match E with
  | .var _ => rwa [Term.TypeVar_open] at xinEop
  | [[λ x : A. E']] =>
    rw [Term.TypeVar_open] at xinEop
    rw [InFreeTermVars, freeTermVars] at xinEop ⊢
    exact of_TypeVar_open xinEop
  | [[E' F]] =>
    rw [Term.TypeVar_open] at xinEop
    exact List.mem_append.mpr <| match List.mem_append.mp xinEop with
    | .inl xinE'op => .inl <| of_TypeVar_open xinE'op
    | .inr xinE'op => .inr <| of_TypeVar_open xinE'op
  | [[Λ a. E']] =>
    rw [Term.TypeVar_open] at xinEop
    rw [InFreeTermVars, freeTermVars] at xinEop ⊢
    exact of_TypeVar_open xinEop
  | [[E' [A] ]] =>
    rw [Term.TypeVar_open] at xinEop
    rw [InFreeTermVars, freeTermVars] at xinEop ⊢
    exact of_TypeVar_open xinEop

end Term.InFreeTermVars

namespace Term.NotInFreeTermVars

theorem lam : [[x ∉ fv(λ y : A. E)]] → [[x ∉ fv(E)]] := (· ·)

theorem app : [[x ∉ fv(E F)]] → ([[x ∉ fv(E)]] ∧ [[x ∉ fv(F)]]) :=
  fun xnin => ⟨(xnin <| List.mem_append.mpr <| .inl ·), (xnin <| List.mem_append.mpr <| .inr ·)⟩

theorem typeGen : [[x ∉ fv(Λ a. E)]] → [[x ∉ fv(E)]] := (· ·)

theorem typeApp : [[x ∉ fv(E [A])]] → [[x ∉ fv(E)]] := (· ·)

theorem TermVar_open_of_ne (h : x ≠ x') : [[x ∉ fv(E)]] → [[x ∉ fv(E^x')]] :=
  (· <| ·.of_TermVar_open h)

theorem TypeVar_open : [[x ∉ fv(E)]] → [[x ∉ fv(E^a)]] := (· ·.of_TypeVar_open)

end Term.NotInFreeTermVars

namespace Term.InFreeTypeVars

theorem of_TermVar_open {E : Term} : InFreeTypeVars a (E.TermVar_open x n) → [[a ∈ ftv(E)]] :=
  fun ainEop => by
  match E with
  | .var _ => nomatch ainEop
  | [[λ x : A. E']] =>
    rw [Term.TermVar_open] at ainEop
    exact List.mem_append.mpr <| match List.mem_append.mp ainEop with
    | .inl ainA => .inl ainA
    | .inr ainE' => .inr <| of_TermVar_open ainE'
  | [[E' F]] =>
    rw [Term.TermVar_open] at ainEop
    exact List.mem_append.mpr <| match List.mem_append.mp ainEop with
    | .inl ainE' => .inl <| of_TermVar_open ainE'
    | .inr ainF => .inr <| of_TermVar_open ainF
  | [[Λ a. E']] =>
    rw [Term.TermVar_open] at ainEop
    rw [InFreeTypeVars, freeTypeVars] at ainEop ⊢
    exact of_TermVar_open ainEop
  | [[E' [A] ]] =>
    rw [Term.TermVar_open] at ainEop
    exact List.mem_append.mpr <| match List.mem_append.mp ainEop with
    | .inl ainE' => .inl <| of_TermVar_open ainE'
    | .inr ainA => .inr ainA

theorem of_TypeVar_open {E : Term} (h : a ≠ a')
  : InFreeTypeVars a (E.TypeVar_open a' n) → [[a ∈ ftv(E)]] := fun ainEop => by
  match E with
  | .var _ => nomatch ainEop
  | [[λ x : A. E']] =>
    rw [Term.TypeVar_open] at ainEop
    exact List.mem_append.mpr <| match List.mem_append.mp ainEop with
    | .inl ainA => .inl <| Type.InFreeTypeVars.of_TypeVar_open h ainA
    | .inr ainE' => .inr <| of_TypeVar_open h ainE'
  | [[E' F]] =>
    rw [Term.TypeVar_open] at ainEop
    exact List.mem_append.mpr <| match List.mem_append.mp ainEop with
    | .inl ainE' => .inl <| of_TypeVar_open h ainE'
    | .inr ainF => .inr <| of_TypeVar_open h ainF
  | [[Λ a. E']] =>
    rw [Term.TypeVar_open] at ainEop
    rw [InFreeTypeVars, freeTypeVars] at ainEop ⊢
    exact of_TypeVar_open h ainEop
  | [[E' [A] ]] =>
    rw [Term.TypeVar_open] at ainEop
    exact List.mem_append.mpr <| match List.mem_append.mp ainEop with
    | .inl ainE' => .inl <| of_TypeVar_open h ainE'
    | .inr ainA => .inr <| Type.InFreeTypeVars.of_TypeVar_open h ainA

end Term.InFreeTypeVars

namespace Term.NotInFreeTypeVars

theorem lam : [[a ∉ ftv(λ x : A. E)]] → [[a ∉ ftv(A)]] ∧ [[a ∉ ftv(E)]] :=
  fun anin => ⟨(anin <| List.mem_append.mpr <| .inl ·), (anin <| List.mem_append.mpr <| .inr ·)⟩

theorem app : [[a ∉ ftv(E F)]] → [[a ∉ ftv(E)]] ∧ [[a ∉ ftv(F)]] :=
  fun anin => ⟨(anin <| List.mem_append.mpr <| .inl ·), (anin <| List.mem_append.mpr <| .inr ·)⟩

theorem typeGen : [[a ∉ ftv(Λ a. E)]] → [[a ∉ ftv(E)]] := (· ·)

theorem typeApp : [[a ∉ ftv(E [A])]] → [[a ∉ ftv(E)]] ∧ [[a ∉ ftv(A)]] :=
  fun anin => ⟨(anin <| List.mem_append.mpr <| .inl ·), (anin <| List.mem_append.mpr <| .inr ·)⟩

theorem TermVar_open : [[a ∉ ftv(E)]] → [[a ∉ ftv(E^x)]] := (· <| ·.of_TermVar_open)

theorem TypeVar_open_of_ne (h : a ≠ a') : [[a ∉ ftv(E)]] → [[a ∉ ftv(E^a')]] :=
  (· <| ·.of_TypeVar_open h)

end Term.NotInFreeTypeVars

namespace TypeWellFormedness

theorem TermVar_drop (Bwf : [[Γ, x : A, Γ' ⊢ B]]) : [[Γ, Γ' ⊢ B]] := match B, Bwf with
  | .var _, var ainΓxAΓ' => match ainΓxAΓ'.append_elim with
    | .inl (.termVarExt ainΓ) => var ainΓ.append_inl
    | .inr ainΓ' => var ainΓ'.append_inr
  | .arr .., arr A'wf B'wf => arr A'wf.TermVar_drop B'wf.TermVar_drop
  | .forall _, .forall A'wf => .forall fun a anin => by
    have := A'wf a anin
    rw [← Environment.append_typeVarExt] at this
    exact this.TermVar_drop

theorem TermVar_intro (Bwf : [[Γ, Γ' ⊢ B]]) : [[Γ, x : A, Γ' ⊢ B]] := match B, Bwf with
  | .var _, var ain => var <| match ain.append_elim with
    | .inl ain' => ain'.termVarExt.append_inl
    | .inr ain' => ain'.append_inr
  | .arr .., arr A'wf B'wf => arr A'wf.TermVar_intro B'wf.TermVar_intro
  | .forall _, .forall A'wf => .forall fun a anin => by
    have := A'wf a anin
    rw [← Environment.append_typeVarExt] at this
    exact this.TermVar_intro

theorem exchange : [[Γ, a, Γ' ⊢ A]] → [[Γ, Γ', a ⊢ A]]
  | var a'in (a := a') => var <| match a'in.append_elim with
    | .inl a'in' => match a'in' with
      | .head => TypeVarInEnvironment.head.append_inr
      | .typeVarExt a'in'' _ => a'in''.append_inl
    | .inr a'in' => by
      by_cases a' = a
      · case pos h =>
        cases h
        exact TypeVarInEnvironment.head.append_inr
      · case neg h => exact a'in'.append_inr.typeVarExt h
  | arr A'wf Bwf => arr A'wf.exchange Bwf.exchange
  | .forall A'wf => .forall fun a' a'nin => by
      have := A'wf a' a'nin
      rw [← Environment.append_typeVarExt] at this
      have := this.exchange
      rw [Environment.append_typeVarExt, Environment.append_typeVarExt,
          ← ((Γ.append Γ').typeVarExt a').append_empty, ← Environment.append_typeVarExt] at this
      exact this.exchange

theorem weakening (Awf : [[Γ ⊢ A]]) : [[Γ', Γ, Γ'' ⊢ A]] := match Awf with
  | var ain => var ain.append_inl.append_inr
  | arr A'wf Bwf => arr A'wf.weakening Bwf.weakening
  | .forall A'wf => .forall fun a anin => by
      rw [← Environment.append_typeVarExt, ← Environment.append_typeVarExt]
      have := A'wf a anin |>.weakening (Γ' := Γ') (Γ := Γ.typeVarExt a) (Γ'' := Γ'')
      rw [Environment.append_assoc, Environment.append_typeVarExt] at this
      rw [Environment.append_assoc]
      exact this.exchange

theorem TypeVarLocallyClosed_of : [[Γ ⊢ A]] → A.TypeVarLocallyClosed 0 := fun Awf =>
  match A, Awf with
  | _, .var _ => .var_free
  | .arr _ _, .arr A'wf Bwf => .arr A'wf.TypeVarLocallyClosed_of Bwf.TypeVarLocallyClosed_of
  | [[∀ a. A']], .forall A'wf (I := I) => by
    let ⟨a, anin⟩ := I.exists_fresh
    have := A'wf a anin |>.TypeVarLocallyClosed_of
    exact .forall <| this.weakening (Nat.le_add_right ..) |>.TypeVar_open_drop <|
      Nat.lt_succ_self _

theorem Type_open_preservation {A : «Type»} {Γ : Environment} (aninftvA : [[a ∉ ftv(A)]])
  (Bwf : [[Γ ⊢ B]])
  : TypeWellFormedness [[Γ, a, Γ']] (A.TypeVar_open a n) →
    TypeWellFormedness [[Γ, Γ' [B / a] ]] (A.Type_open B n) :=
  fun Aopwf => by match A with
  | .var (.free a') =>
    rw [Type.TypeVar_open, if_neg nofun] at Aopwf
    let .var a'inaΓ := Aopwf
    match a'inaΓ.append_elim with
    | .inl .head => nomatch List.not_mem_singleton.mp aninftvA
    | .inl (.typeVarExt a'inΓ a'nea) => exact var a'inΓ.append_inl
    | .inr a'inΓ => exact .var a'inΓ.TypeVar_subst.append_inr
  | .var (.bound _) =>
    rw [Type.Type_open]
    split
    · case isTrue h =>
      have := Bwf.weakening (Γ' := .empty) (Γ'' := Γ'.TypeVar_subst a B)
      rw [Environment.empty_append] at this
      exact this
    · case isFalse h =>
      rw [Type.TypeVar_open, if_neg h] at Aopwf
      nomatch Aopwf
  | [[A' → B']] =>
    rw [Type.TypeVar_open] at Aopwf
    let .arr A'wf B'wf := Aopwf
    exact .arr (Type_open_preservation (Type.NotInFreeTypeVars.arr.mp aninftvA).left Bwf A'wf)
      (Type_open_preservation (Type.NotInFreeTypeVars.arr.mp aninftvA).right Bwf B'wf)
  | [[∀ a. A']] =>
    rw [Type.TypeVar_open] at Aopwf
    let .forall A'wf (I := I) := Aopwf
    exact .forall (I := a :: I) <| fun a' a'nin => by
      have a'nea := List.ne_of_not_mem_cons a'nin
      have := A'wf a' <| List.not_mem_of_not_mem_cons a'nin
      rw [← Bwf.TypeVarLocallyClosed_of.TypeVar_open_Type_open_comm (Nat.zero_ne_add_one _)]
      rw [A'.TypeVar_open_comm (Nat.succ_ne_zero _),
          ← Environment.append_typeVarExt] at this
      exact Type_open_preservation (aninftvA.forall.TypeVar_open_of_ne a'nea.symm) Bwf this

theorem TypeVar_subst_preservation {A : «Type»} {Γ : Environment} (Bwf : [[ε ⊢ B]])
  : [[ε, a, Γ ⊢ A]] → [[Γ [B / a] ⊢ A [B / a] ]] :=
  fun Aopwf => by match A with
  | .var (.free a') =>
    let .var a'inεaΓ := Aopwf
    rw [Type.TypeVar_subst]
    split
    · case isTrue h =>
      have := Bwf.weakening (Γ' := .empty) (Γ'' := Γ.TypeVar_subst a B)
      rw [Environment.empty_append, Environment.empty_append] at this
      exact this
    · case isFalse h =>
      match a'inεaΓ.append_elim with
      | .inl .head => contradiction
      | .inr a'inΓ => exact TypeWellFormedness.var a'inΓ.TypeVar_subst
  | .var (.bound _) => nomatch Aopwf
  | [[A' → B']] =>
    let .arr A'wf B'wf := Aopwf
    exact .arr (TypeWellFormedness.TypeVar_subst_preservation Bwf A'wf)
      (TypeWellFormedness.TypeVar_subst_preservation Bwf B'wf)
  | [[∀ a. A']] =>
    let .forall A'wf (I := I) := Aopwf
    rw [Type.TypeVar_subst]
    exact .forall (I := a :: I) fun a' a'nin => by
      have a'nea := List.ne_of_not_mem_cons a'nin
      have := A'wf a' <| List.not_mem_of_not_mem_cons a'nin
      rw [← Environment.TypeVar_subst,
          Bwf.TypeVarLocallyClosed_of.TypeVar_subst_TypeVar_open_comm a'nea.symm]
      rw [← Environment.append_typeVarExt] at this
      exact TypeVar_subst_preservation Bwf this

end TypeWellFormedness

namespace TermVarNotInEnvironmentDomain

theorem TermVar_drop : [[x ∉ dom(ε, x' : A, Γ)]] → [[x ∉ dom(Γ)]] :=
  fun xnindomεxAΓ => by
  match Γ with
  | [[ε]] => nofun
  | [[Γ', x'' : A']] =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindomεxAΓ ⊢
    rw [Environment.termVar_domain_append] at xnindomεxAΓ
    let ⟨xnindomΓ, _⟩ := List.not_mem_append'.mp xnindomεxAΓ
    exact xnindomΓ
  | [[Γ', a]] =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindomεxAΓ ⊢
    rw [Environment.termVar_domain_append] at xnindomεxAΓ
    let ⟨xnindomΓ, _⟩ := List.not_mem_append'.mp xnindomεxAΓ
    exact xnindomΓ

theorem TypeVar_drop : [[x ∉ dom(ε, a, Γ)]] → [[x ∉ dom(Γ)]] := fun xnindomεaΓ => by
  match Γ with
  | .empty => nofun
  | [[Γ', x' : A']] =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindomεaΓ ⊢
    rw [Environment.termVar_domain_append] at xnindomεaΓ
    let ⟨xnindomΓ, _⟩ := List.not_mem_append'.mp xnindomεaΓ
    exact xnindomΓ
  | [[Γ', a']] =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindomεaΓ ⊢
    rw [Environment.termVar_domain_append] at xnindomεaΓ
    let ⟨xnindomΓ, _⟩ := List.not_mem_append'.mp xnindomεaΓ
    exact xnindomΓ

theorem TypeVar_subst : [[x ∉ dom(Γ)]] → [[x ∉ dom(Γ [A / a])]] := fun xnindom => by
  match Γ with
  | [[ε]] => nofun
  | [[Γ', x' : A']] =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindom ⊢
    rw [Environment.TypeVar_subst, Environment.termVar_domain]
    rw [Environment.termVar_domain] at xnindom
    let xnex' := List.ne_of_not_mem_cons xnindom
    let xnindomΓ' := List.not_mem_of_not_mem_cons xnindom
    have : [[x ∉ dom(Γ')]] := by
      dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain]
      exact xnindomΓ'
    exact List.not_mem_cons_of_ne_of_not_mem xnex' this.TypeVar_subst
  | [[Γ', a']] =>
    dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain] at xnindom ⊢
    rw [Environment.TypeVar_subst, Environment.termVar_domain]
    rw [Environment.termVar_domain] at xnindom
    have : [[x ∉ dom(Γ')]] := by
      dsimp only [TermVarNotInEnvironmentDomain, TermVarInEnvironmentDomain]
      exact xnindom
    exact this.TypeVar_subst

end TermVarNotInEnvironmentDomain

namespace TypeVarNotInEnvironmentDomain

theorem TermVar_drop : [[a ∉ dom(ε, x : A, Γ)]] → [[a ∉ dom(Γ)]] :=
  fun anindomεxAΓ => by
  match Γ with
  | [[ε]] => nofun
  | [[Γ', x' : A']] =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindomεxAΓ ⊢
    rw [Environment.typeVar_domain_append] at anindomεxAΓ
    let ⟨anindomΓ, _⟩ := List.not_mem_append'.mp anindomεxAΓ
    exact anindomΓ
  | [[Γ', a]] =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindomεxAΓ ⊢
    rw [Environment.typeVar_domain_append] at anindomεxAΓ
    let ⟨anindomΓ, _⟩ := List.not_mem_append'.mp anindomεxAΓ
    exact anindomΓ

theorem TypeVar_drop : [[a ∉ dom(ε, a', Γ)]] → [[a ∉ dom(Γ)]] := fun anindomεa'Γ => by
  match Γ with
  | [[ε]] => nofun
  | [[Γ', x' : A']] =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindomεa'Γ ⊢
    rw [Environment.typeVar_domain_append] at anindomεa'Γ
    let ⟨anindomΓ, _⟩ := List.not_mem_append'.mp anindomεa'Γ
    exact anindomΓ
  | [[Γ', a'']] =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindomεa'Γ ⊢
    rw [Environment.typeVar_domain_append] at anindomεa'Γ
    let ⟨anindomΓ, _⟩ := List.not_mem_append'.mp anindomεa'Γ
    exact anindomΓ

theorem TypeVar_subst : [[a ∉ dom(Γ)]] → [[a ∉ dom(Γ [A / a'])]] := fun anindom => by
  match Γ with
  | [[ε]] => nofun
  | [[Γ', x' : A']] =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindom ⊢
    rw [Environment.TypeVar_subst, Environment.typeVar_domain]
    rw [Environment.typeVar_domain] at anindom
    have : [[a ∉ dom(Γ')]] := by
      dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain]
      exact anindom
    exact this.TypeVar_subst
  | [[Γ', a']] =>
    dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain] at anindom ⊢
    rw [Environment.TypeVar_subst, Environment.typeVar_domain]
    rw [Environment.typeVar_domain] at anindom
    let xnex' := List.ne_of_not_mem_cons anindom
    let anindomΓ' := List.not_mem_of_not_mem_cons anindom
    have : [[a ∉ dom(Γ')]] := by
      dsimp only [TypeVarNotInEnvironmentDomain, TypeVarInEnvironmentDomain]
      exact anindomΓ'
    exact List.not_mem_cons_of_ne_of_not_mem xnex' this.TypeVar_subst

end TypeVarNotInEnvironmentDomain

namespace EnvironmentWellFormedness

theorem TermVar_drop : [[⊢ ε, x : A, Γ]] → [[⊢ Γ]] := fun εxAΓwf => by match Γ, εxAΓwf with
  | [[ε]], _ => exact empty
  | [[Γ', x' : A']], termVarExt Γ'wf A'wf x'nindom =>
    have := A'wf.TermVar_drop (Γ := .empty)
    rw [Environment.empty_append] at this
    exact termVarExt Γ'wf.TermVar_drop this x'nindom.TermVar_drop
  | [[Γ', a]], typeVarExt Γ'wf anindom =>
    exact typeVarExt Γ'wf.TermVar_drop anindom.TermVar_drop

theorem TypeVar_subst_preservation (Awf : [[ε ⊢ A]]) : [[⊢ ε, a, Γ]] → [[⊢ Γ [A / a] ]] :=
  fun εaΓwf => by
  match Γ, εaΓwf with
  | [[ε]], _ =>
    rw [Environment.TypeVar_subst]
    exact .empty
  | [[Γ', x' : A']], termVarExt εaΓ'wf A'wf x'nindom =>
    rw [Environment.TypeVar_subst]
    exact termVarExt (εaΓ'wf.TypeVar_subst_preservation Awf) (.TypeVar_subst_preservation Awf A'wf)
      x'nindom.TypeVar_drop.TypeVar_subst
  | [[Γ', a']], typeVarExt εaΓ'wf a'nindom =>
    rw [Environment.TypeVar_subst]
    exact typeVarExt (εaΓ'wf.TypeVar_subst_preservation Awf) a'nindom.TypeVar_drop.TypeVar_subst

end EnvironmentWellFormedness

theorem TypeWellFormedness.TypeVar_intro : [[Γ, Γ' ⊢ A]] → [[Γ, a, Γ' ⊢ A]]
  | var ain (a := a') => var <| match ain.append_elim with
    | .inl ain' => by
      by_cases a' = a
      · case pos h =>
        cases h
        exact TypeVarInEnvironment.head.append_inl
      · case neg h =>
        exact ain'.typeVarExt h |>.append_inl
    | .inr ain' => ain'.append_inr
  | arr A'wf Bwf => arr A'wf.TypeVar_intro Bwf.TypeVar_intro
  | .forall A'wf => .forall fun a' a'nin => by
      rw [← Environment.append_typeVarExt]
      have := A'wf a' a'nin
      rw [← Environment.append_typeVarExt] at this
      exact this.TypeVar_intro

theorem TypeWellFormedness.of_TermVarInEnvironment_of_EnvironmentWellFormedness
  (xAinΓ : [[x : A ∈ Γ]]) (Γwf : [[⊢ Γ]]) : [[Γ ⊢ A]] := match xAinΓ, Γwf with
  | .head, .termVarExt _ Awf _ => Awf.TermVar_intro (Γ' := .empty)
  | .termVarExt xAinΓ' _, .termVarExt Γ'wf _ _ =>
    of_TermVarInEnvironment_of_EnvironmentWellFormedness xAinΓ' Γ'wf |>.TermVar_intro (Γ' := .empty)
  | .typeVarExt xAinΓ', .typeVarExt Γ'wf _ =>
    of_TermVarInEnvironment_of_EnvironmentWellFormedness xAinΓ' Γ'wf |>.TypeVar_intro (Γ' := .empty)

namespace Typing

theorem TermVarLocallyClosed_of_empty : [[ε ⊢ E : A]] → E.TermVarLocallyClosed 0 := go
where
  go {Γ : Environment} {E : Term} {A : «Type»}
    : [[Γ ⊢ E : A]] → E.TermVarLocallyClosed Γ.termVar_count := fun EtyA => match E, EtyA with
    | _, .var .. => .var_free
    | [[λ x : A'. E']], .lam _ E'ty (I := I) => by
      let ⟨x, xnin⟩ := I.exists_fresh
      have := go <| E'ty x xnin
      rw [Environment.termVar_count, Nat.add_comm] at this
      exact .lam <| this.TermVar_open_drop <| Nat.zero_lt_succ _
    | .app .., .app E'ty Fty => .app (go E'ty) (go Fty)
    | [[Λ a. E']], .typeGen E'ty (I := I) => by
      let ⟨a, anin⟩ := I.exists_fresh
      exact .typeGen <| go (E'ty a anin) |>.TypeVar_open_drop
    | [[E' [A'] ]], .typeApp E'ty _ => .typeApp <| go E'ty

theorem TypeVarLocallyClosed_of_empty : [[ε ⊢ E : A]] → E.TypeVarLocallyClosed 0 := go
where
  go {Γ : Environment} {E : Term} {A : «Type»}
    : [[Γ ⊢ E : A]] → E.TypeVarLocallyClosed Γ.typeVar_count := fun EtyA => match E, EtyA with
    | _, .var .. => .var
    | [[λ x : A'. E']], .lam A'ty E'ty (I := I) => by
      let A'lc := A'ty.TypeVarLocallyClosed_of.weakening (Nat.le_add_left ..) (n := Γ.typeVar_count)
      let ⟨x, xnin⟩ := I.exists_fresh
      have := go <| E'ty x xnin
      rw [Environment.typeVar_count] at this
      exact .lam A'lc this.TermVar_open_drop
    | .app .., .app E'ty Fty => .app (go E'ty) (go Fty)
    | [[Λ a. E']], .typeGen E'ty (I := I) => by
      let ⟨a, anin⟩ := I.exists_fresh
      have := go <| E'ty a anin
      rw [Environment.typeVar_count, Nat.add_comm] at this
      apply Term.TypeVarLocallyClosed.typeGen
      exact this.TypeVar_open_drop <| Nat.zero_lt_succ _
    | [[E' [A'] ]], .typeApp E'ty A'ty => by
      let A'lc := A'ty.TypeVarLocallyClosed_of.weakening (Nat.le_add_left ..) (n := Γ.typeVar_count)
      exact .typeApp (go E'ty) A'lc

theorem TypeWellFormedness_of : [[Γ ⊢ E : A]] → [[Γ ⊢ A]] := fun EtyA => by match E, A, EtyA with
  | .var _, _, .var Γwf ainΓ =>
    exact .of_TermVarInEnvironment_of_EnvironmentWellFormedness ainΓ Γwf
  | [[λ x : A'. E']], .arr _ B, .lam A'wf E'ty (I := I) =>
    let ⟨x, xnin⟩ := I.exists_fresh
    exact .arr A'wf <| E'ty x xnin |>.TypeWellFormedness_of.TermVar_drop (Γ' := .empty)
  | [[E' F]], A, .app E'ty _ =>
    let .arr _ Awf := E'ty.TypeWellFormedness_of
    exact Awf
  | [[Λ a. E']], [[∀ a. A']], .typeGen E'ty =>
    exact .forall (E'ty · · |>.TypeWellFormedness_of)
  | [[E' [B] ]], A, EtyA =>
    let .typeApp E'ty Bwf (A := A') := EtyA
    let .forall A'wf (I := I) := E'ty.TypeWellFormedness_of
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    exact .Type_open_preservation (Γ' := .empty) aninA' Bwf <| A'wf a aninI

theorem weakening (EtyA : [[Γ ⊢ E : A]]) (Γ'Γwf : [[⊢ Γ', Γ]]) : [[Γ', Γ ⊢ E : A]] :=
  match EtyA with
  | var _ xin => var Γ'Γwf xin.append_inr
  | lam Awf E'ty (I := I) =>
    lam (Awf.weakening (Γ'' := .empty)) (I := [[Γ', Γ]].termVar_domain ++ I) fun x xnin =>
      let ⟨xnindom, xninI⟩ := List.not_mem_append'.mp xnin
      E'ty x xninI |>.weakening <| Γ'Γwf.termVarExt (Awf.weakening (Γ'' := .empty)) xnindom
  | app E'ty Fty => app (E'ty.weakening Γ'Γwf) (Fty.weakening Γ'Γwf)
  | typeGen E'ty (I := I) => typeGen (I := [[Γ', Γ]].typeVar_domain ++ I) fun a anin =>
      let ⟨anindom, aninI⟩ := List.not_mem_append'.mp anin
      E'ty a aninI |>.weakening <| Γ'Γwf.typeVarExt anindom
  | typeApp E'ty Bwf => typeApp (E'ty.weakening Γ'Γwf) <| Bwf.weakening (Γ'' := .empty)

theorem Term_open_preservation {E : Term} (EtyB : Typing [[ε, x : A, Γ]] (E.TermVar_open x n) B)
  (xninΓ : [[x ∉ Γ]]) (xninfvE : [[x ∉ fv(E)]]) (FtyA : [[ε ⊢ F : A]])
  : Typing Γ (E.Term_open F n) B := by
  match E with
  | .var (.free _) =>
    rw [Term.Term_open, if_neg nofun]
    let .var εxAΓwf x'BinεxAΓ := EtyB
    match x'BinεxAΓ.append_elim with
    | .inl ⟨.head, _⟩ => nomatch List.not_mem_singleton.mp xninfvE
    | .inr xBinΓ => exact var εxAΓwf.TermVar_drop xBinΓ
  | .var (.bound _) =>
    rw [Term.Term_open]
    split
    · case isTrue h =>
      rw [← h, Term.TermVar_open, if_pos rfl] at EtyB
      let .var εxAΓwf xBinxAΓ := EtyB
      match xBinxAΓ.append_elim with
      | .inl ⟨.head, _⟩ => exact FtyA.weakening εxAΓwf.TermVar_drop
      | .inr xBinΓ => exact xninΓ _ xBinΓ |>.elim
    · case isFalse h =>
      rw [Term.TermVar_open, if_neg h] at EtyB
      nomatch EtyB
  | [[λ x : A'. E']] =>
    rw [Term.Term_open]
    let .lam A'wf E'ty (I := I) := EtyB
    rw [← Γ.empty_append]
    exact lam (I := x :: I) A'wf.TermVar_drop fun x' x'nin => by
      have x'nex := List.ne_of_not_mem_cons x'nin
      have := E'ty x' <| List.not_mem_of_not_mem_cons x'nin
      rw [Environment.empty_append,
          ← FtyA.TermVarLocallyClosed_of_empty.TermVar_open_Term_open_id (Nat.zero_ne_add_one _)]
      rw [← Environment.append_termVarExt, E'.TermVar_open_comm (Nat.succ_ne_zero _)] at this
      exact this.Term_open_preservation (xninΓ.termVarExt x'nex.symm)
        (xninfvE.lam.TermVar_open_of_ne x'nex.symm) FtyA
  | [[E' F]] =>
    let .app E'ty Fty := EtyB
    rw [Term.Term_open]
    exact app (E'ty.Term_open_preservation xninΓ xninfvE.app.left FtyA)
      (Fty.Term_open_preservation xninΓ xninfvE.app.right FtyA)
  | [[Λ a. E']] =>
    let .typeGen E'ty := EtyB
    rw [Term.Term_open]
    exact typeGen fun a anin => by
      have := E'ty a anin
      rw [← FtyA.TypeVarLocallyClosed_of_empty.TypeVar_open_Term_open_comm]
      rw [← Environment.append_typeVarExt, E'.TermVar_open_TypeVar_open_comm] at this
      exact this.Term_open_preservation xninΓ.typeVarExt
        xninfvE.typeGen.TypeVar_open FtyA
  | [[E' [A'] ]] =>
    let .typeApp E'ty A'wf := EtyB
    have := A'wf.TermVar_drop
    rw [Γ.empty_append] at this
    exact typeApp (E'ty.Term_open_preservation xninΓ xninfvE.typeApp FtyA) this

theorem lam_arr_eq : [[Γ ⊢ λ x : A. E : A' → B]] → A = A' | .lam .. => rfl

theorem Type_open_preservation {E : Term} {A : «Type»}
  (EtyA : Typing [[ε, a, Γ]] (E.TypeVar_open a n) (A.TypeVar_open a n)) (aninΓ : [[a ∉ Γ]])
  (aninftvE : [[a ∉ ftv(E)]]) (aninftvA : [[a ∉ ftv(A)]]) (Bwf : [[ε ⊢ B]])
  : Typing [[(Γ [B / a])]] (E.Type_open B n) (A.Type_open B n) := by match E, A, EtyA with
  | .var (.free x), A, .var εaΓwf xAopinεaΓ =>
    exact var (εaΓwf.TypeVar_subst_preservation Bwf) <| xAopinεaΓ.TypeVar_subst aninftvA
  | [[λ x : A''. E'']], [[A''' → B']], EtyA =>
    rw [Term.Type_open, Type.Type_open]
    rw [Term.TypeVar_open, Type.TypeVar_open] at EtyA
    cases Type.NotInFreeTypeVars.TypeVar_open_inj_of aninftvE.lam.left
      (Type.NotInFreeTypeVars.arr.mp aninftvA).left EtyA.lam_arr_eq
    let .lam A''wf E''ty := EtyA
    let A''wf' := TypeWellFormedness.Type_open_preservation aninftvE.lam.left Bwf A''wf
    rw [Environment.empty_append] at A''wf'
    exact .lam A''wf' fun x xnin => by
      rw [← E''.TermVar_open_Type_open_comm]
      have := E''ty x xnin
      rw [← Environment.append_termVarExt, ← Term.TermVar_open_TypeVar_open_comm] at this
      have := this.Type_open_preservation aninΓ.termVarExt aninftvE.lam.right.TermVar_open
        (Type.NotInFreeTypeVars.arr.mp aninftvA).right Bwf
      rw [Environment.TypeVar_subst,
          aninftvE.lam.left.TypeVar_open_TypeVar_subst_eq_Type_open_of] at this
      exact this
  | [[E'' F]], A, .app E''ty Fty (A := A'') =>
    rw [Term.Type_open]
    let A''arrAoplc :=
      E''ty.TypeWellFormedness_of.TypeVarLocallyClosed_of.weakening (Nat.le_add_left ..) (n := n)
    rw [← A''arrAoplc.TypeVar_open_TypeVar_close_id (a := a) (n := n), Type.TypeVar_close,
        aninftvA.TypeVar_close_TypeVar_open_of] at E''ty
    let .arr A''lc _ := A''arrAoplc
    rw [← A''lc.TypeVar_open_TypeVar_close_id (a := a) (n := n)] at Fty
    let E''ty' := E''ty.Type_open_preservation aninΓ aninftvE.app.left
      (Type.NotInFreeTypeVars.arr.mpr ⟨Type.NotInFreeTypeVars.of_TypeVar_close, aninftvA⟩) Bwf
    let Fty' := Fty.Type_open_preservation aninΓ aninftvE.app.right
      Type.NotInFreeTypeVars.of_TypeVar_close Bwf
    exact .app E''ty' Fty'
  | [[Λ a. E']], [[∀ a. A']], .typeGen E'ty (I := I) =>
    exact .typeGen (I := a :: I) fun a' a'nin => by
      have a'nea := List.ne_of_not_mem_cons a'nin
      have := E'ty a' <| List.not_mem_of_not_mem_cons a'nin
      rw [← E'.TypeVar_open_Type_open_comm Bwf.TypeVarLocallyClosed_of (Nat.zero_ne_add_one _),
          ← Bwf.TypeVarLocallyClosed_of.TypeVar_open_Type_open_comm (Nat.zero_ne_add_one _)]
      rw [← Environment.append_typeVarExt, E'.TypeVar_open_comm (Nat.succ_ne_zero _),
          A'.TypeVar_open_comm (Nat.succ_ne_zero _)] at this
      exact this.Type_open_preservation (Γ := Γ.typeVarExt a')
        (aninΓ.typeVarExt a'nea.symm)
        (aninftvE.typeGen.TypeVar_open_of_ne a'nea.symm)
        (aninftvA.forall.TypeVar_open_of_ne a'nea.symm) Bwf
  | [[E' [B'] ]], A, EtyA =>
    rw [Term.Type_open]
    generalize A'eq : A.TypeVar_open a n = A' at EtyA
    let .typeApp E'ty B'wf (A := A'') := EtyA
    let A''wf := E'ty.TypeWellFormedness_of
    let A''folc := A''wf.TypeVarLocallyClosed_of
    let A''folc' := A''folc.weakening (Nat.le_add_left ..) (n := n)
    rw [← A''folc'.TypeVar_open_TypeVar_close_id (a := a)] at E'ty
    let E'ty' := E'ty.Type_open_preservation aninΓ aninftvE.typeApp.left
      Type.NotInFreeTypeVars.of_TypeVar_close Bwf
    let B'wf' := TypeWellFormedness.Type_open_preservation aninftvE.typeApp.right Bwf B'wf
    rw [Environment.empty_append] at B'wf'
    let .forall A''lc' := A''folc'
    rw [Type.TypeVar_close, Type.Type_open,
        A''lc'.TypeVar_close_Type_open_eq_TypeVar_subst] at E'ty'
    rw [Type.Type_open_TypeVar_subst_eq_of_TypeVar_open_eq A'eq Bwf.TypeVarLocallyClosed_of
          aninftvA aninftvE.typeApp.right]
    exact Typing.typeApp E'ty' B'wf'

end Typing

namespace OperationalSemantics

theorem preservation (EtyA : [[ε ⊢ E : A]]) (EstepF : [[E -> F]]) : [[ε ⊢ F : A]] :=
  match EstepF, EtyA with
  | appl E'stepE'next, .app E'tyA'arrA FtyA' => .app (E'stepE'next.preservation E'tyA'arrA) FtyA'
  | appr FstepFnext, .app VtyA'arrA FtyA' => .app VtyA'arrA <| FstepFnext.preservation FtyA'
  | lamApp, .app (.lam _ E'tyA (E := E') (I := I)) VtyA'' =>
    let ⟨x, xnin⟩ := E'.freeTermVars ++ I |>.exists_fresh
    let ⟨xninE', xninI⟩ := List.not_mem_append'.mp xnin
    .Term_open_preservation (E'tyA x xninI) nofun xninE' VtyA''
  | typeApp E'stepE'next, .typeApp E'ty A'wf => .typeApp (E'stepE'next.preservation E'ty) A'wf
  | typeGenApp, .typeApp (.typeGen E'tyA'' (E := E') (A := A'') (I := I)) A'wf =>
    let ⟨a, anin⟩ := E'.freeTypeVars ++ A''.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninE'A'', aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninE', aninA''⟩ := List.not_mem_append'.mp aninE'A''
    .Type_open_preservation (Γ := .empty) (E'tyA'' a aninI) nofun aninE' aninA'' A'wf

theorem progress (EtyA : [[ε ⊢ E : A]]) : E.IsValue ∨ ∃ F, [[E -> F]] := match E, EtyA with
  | [[λ x : A. E']], _ => .inl .lam
  | [[E' F']], .app E'tyA'arrA F'tyA' => match progress E'tyA'arrA with
    | .inl E'IsValue => match progress F'tyA' with
      | .inl F'IsValue =>
        let [[λ x : A'. E'']] := E'
        .inr <| .intro _ <| lamApp (V := ⟨F', F'IsValue⟩)
      | .inr ⟨_, F'stepF'_next⟩ => .inr <| .intro _ <| appr F'stepF'_next (V := ⟨E', E'IsValue⟩)
    | .inr ⟨_, E'stepE'_next⟩ => .inr <| .intro _ <| appl E'stepE'_next
  | [[Λ a. E']], _ => .inl .typeGen
  | [[E' [B] ]], .typeApp E'ty _ => match progress E'ty with
    | .inl _ => let [[Λ a. E'']] := E'; .inr <| .intro _ typeGenApp
    | .inr ⟨_, E'stepE'_next⟩ => .inr <| .intro _ <| typeApp E'stepE'_next

end OperationalSemantics

end LottExamples.SystemF
