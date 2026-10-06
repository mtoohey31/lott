import Aesop
import Lott.Data.List
import LottExamples.STLC.Semantics

namespace LottExamples.STLC

namespace Term

@[simp]
theorem Var_open_sizeOf : sizeOf (Var_open e x n) = sizeOf e := by
  induction e generalizing n <;> aesop (add simp Var_open)

theorem Var_open_comm (e : Term)
  : m ≠ n → (e.Var_open x m).Var_open x' n = (e.Var_open x' n).Var_open x m := by
  induction e generalizing m n <;> aesop (add simp Var_open)

namespace VarLocallyClosed

theorem weakening (elc : VarLocallyClosed e m) : m ≤ n → e.VarLocallyClosed n := by
  induction elc generalizing n <;> aesop
    (add 20% constructors VarLocallyClosed, 20% Nat.lt_of_lt_of_le)

theorem Var_open_drop : m < n → (Var_open e x m).VarLocallyClosed n → e.VarLocallyClosed n := by
  induction e generalizing m n <;> aesop
    (add simp Var_open, safe cases VarLocallyClosed, safe constructors VarLocallyClosed)

theorem Var_open_id : VarLocallyClosed e n → e.Var_open x n = e := by
  induction e generalizing n <;> aesop (add simp Term.Var_open, safe cases VarLocallyClosed)

theorem Var_open_Term_open_comm (e'lc : VarLocallyClosed e')
  : m ≠ n → (Term_open e e' m).Var_open x n = (e.Var_open x n).Term_open e' m := by
  induction e generalizing m n <;> aesop
    (add simp [Term.Var_open, Term_open], 50% apply Nat.zero_le, 20% apply [Var_open_id, weakening])

end VarLocallyClosed

theorem freeVars_Var_open_subset : freeVars (Var_open e x n) ⊆ x :: freeVars e := by
  induction e generalizing n with
  | app _ _ e₀ih e₁ih =>
    simp [Var_open, freeVars]
    constructor
    case' left => apply e₀ih.trans
    case' right => apply e₁ih.trans
    all_goals simp
  | _ => aesop (add simp [Var_open, freeVars])

theorem mem_freeVars_Var_open_drop : x ∈ freeVars (Var_open e x' n) → x ≠ x' → x ∈ freeVars e := by
  intro mem ne
  cases freeVars_Var_open_subset mem <;> trivial

theorem not_mem_freeVars_Var_open_intro (xnin : x ∉ freeVars e) (xne : x ≠ x') :
  x ∉ freeVars (Var_open e x' n) := (xnin <| mem_freeVars_Var_open_drop · xne)

end Term

namespace Environment

theorem append_assoc {Γ₀ : Environment} : [[Γ₀, (Γ₁, Γ₂)]] = [[(Γ₀, Γ₁), Γ₂]] := by
  cases Γ₂ with
  | empty => rfl
  | ext => rw [append, append, append_assoc, ← append]

theorem NotMem.ext : [[x ∉ Γ, x' : τ]] ↔ x ≠ x' ∧ [[x ∉ Γ]] where
  mp xnin :=
    have ne : x ≠ x' := fun | .refl _ => xnin ⟨_, .head⟩
    ⟨ne, fun ⟨_, xin⟩ => xnin ⟨_, .ext xin ne⟩⟩
  mpr := by
    rintro ⟨ne, xnin⟩ ⟨_, ⟨⟩ | xin⟩
    · nomatch ne
    · exact xnin ⟨_, xin⟩

namespace Mem

theorem append_elim (xin : [[x : τ ∈ Γ₀, Γ₁]]) : [[x : τ ∈ Γ₀]] ∧ [[x ∉ Γ₁]] ∨ [[x : τ ∈ Γ₁]] :=
  match Γ₁ with
  | .empty => .inl ⟨xin, nofun⟩
  | .ext .. => match xin with
    | head => .inr head
    | ext xin xne => match append_elim xin with
      | .inl ⟨xin, xnin⟩ => .inl ⟨xin, NotMem.ext.mpr ⟨xne, xnin⟩⟩
      | .inr xin => .inr <| ext xin xne

theorem append_inl (xin : [[x : τ ∈ Γ₀]]) (xnin : [[x ∉ Γ₁]]) : [[x : τ ∈ Γ₀, Γ₁]] :=
  match Γ₁ with
  | .empty => xin
  | .ext .. =>
    have ⟨xne, xnin⟩ := NotMem.ext.mp xnin
    ext (append_inl xin xnin) xne

theorem append_inr : [[x : τ ∈ Γ₁]] → [[x : τ ∈ Γ₀, Γ₁]]
  | head => head
  | ext xin xne => ext (append_inr xin) xne

theorem dom : [[x : τ ∈ Γ]] → x ∈ dom Γ
  | .head => .head _
  | .ext mem _ => .tail _ <| dom mem

end Mem

namespace Mem'

theorem append_elim (xin : [[x ∈ Γ₀, Γ₁]]) : [[x ∈ Γ₀]] ∨ [[x ∈ Γ₁]] :=
  xin.choose_spec.append_elim.imp (.intro _ ∘ And.left) (.intro _)

theorem append_inr : [[x ∈ Γ₁]] → [[x ∈ Γ₀, Γ₁]] := .imp fun _ => .append_inr

theorem append_inl : [[x ∈ Γ₀]] → [[x ∈ Γ₀, Γ₁]] := by
  if [[x ∈ Γ₁]] then
    exact fun _ => append_inr ‹_›
  else
    exact .imp fun _ => .append_inl (xnin := ‹_›)

end Mem'

namespace NotMem

theorem append : [[x ∉ Γ₀, Γ₁]] ↔ [[x ∉ Γ₀]] ∧ [[x ∉ Γ₁]] where
  mp xnin := ⟨(xnin ·.append_inl), (xnin ·.append_inr)⟩
  mpr | ⟨xninΓ₀, xninΓ₁⟩, xin => xin.append_elim.elim xninΓ₀ xninΓ₁

theorem drop : [[x ∉ Γ₀, x' : τ, Γ₁]] → [[x ∉ Γ₀, Γ₁]] :=
  append.mpr ∘ And.imp_left (And.right ∘ NotMem.ext.mp) ∘ append.mp 

theorem exchange (xnin : [[x ∉ Γ₀, x' : τ, Γ₁, Γ₂]]) : [[x ∉ Γ₀, Γ₁, x' : τ, Γ₂]] :=
  have ⟨xninΓ₀x', xninΓ₁Γ₂⟩ := append.mp xnin
  have ⟨xne, xninΓ₀⟩ := ext.mp xninΓ₀x'
  have ⟨xninΓ₁, xninΓ₂⟩ := append.mp xninΓ₁Γ₂
  append.mpr ⟨xninΓ₀, append.mpr ⟨ext.mpr ⟨xne, xninΓ₁⟩, xninΓ₂⟩⟩

end NotMem

namespace WellFormedness

theorem insert (wf : [[⊢ Γ₀, Γ₁]]) (xnin : [[x ∉ Γ₀, Γ₁]]) : [[⊢ Γ₀, x : τ, Γ₁]] :=
  match Γ₁ with
  | [[ε]] => wf.ext xnin
  | [[Γ₁', x' : τ']] =>
    have .ext wf' x'nin := wf
    have ⟨x'ninΓ₀, x'ninΓ₁'⟩ := NotMem.append.mp x'nin
    have ⟨_, xninΓ₁⟩ := NotMem.append.mp xnin
    ext (insert wf' (NotMem.ext.mp xnin).right) <|
      NotMem.append.mpr ⟨NotMem.ext.mpr ⟨NotMem.ext.mp xninΓ₁ |>.left.symm, x'ninΓ₀⟩, x'ninΓ₁'⟩

theorem drop : {Γ₁ : _} → [[⊢ Γ₀, x : τ, Γ₁]] → [[⊢ Γ₀, Γ₁]]
  | .empty, ext wf' _ => wf'
  | .ext .., ext wf' x'nin => ext (drop wf') x'nin.drop

theorem append_elim : [[⊢ Γ₀, Γ₁]] → [[⊢ Γ₀]] ∧ [[⊢ Γ₁]] := fun Γ₀Γ₁wf =>
  match Γ₁ with
  | .empty => ⟨Γ₀Γ₁wf, .empty⟩
  | .ext .. =>
    have .ext Γ₀Γ₁'wf xninΓ₀Γ₁' := Γ₀Γ₁wf
    have ⟨Γ₀wf, Γ₁'wf⟩ := Γ₀Γ₁'wf.append_elim
    ⟨Γ₀wf, .ext Γ₁'wf <| NotMem.append.mp xninΓ₀Γ₁' |>.right⟩

theorem exchange (wf : [[⊢ Γ₀, x : τ, Γ₁, Γ₂]]) : [[⊢ Γ₀, Γ₁, x : τ, Γ₂]] := by cases Γ₂ with
  | empty => cases Γ₁ with
    | empty => exact wf
    | ext =>
      have .ext wf' x'nin := wf
      have ⟨x'nin', _⟩ := NotMem.append.mp x'nin
      cases NotMem.ext.mp x'nin'
      replace .ext wf' xnin := exchange wf' (Γ₂ := [[ε]])
      cases NotMem.append.mp xnin
      exact ext (ext wf' (NotMem.append.mpr ⟨‹_›, ‹_›⟩))
        (NotMem.ext.mpr ⟨.symm ‹_›, NotMem.append.mpr ⟨‹_›, ‹_›⟩⟩)
  | ext =>
    have .ext wf' x'nin := wf
    exact ext (exchange wf') x'nin.exchange

end WellFormedness

theorem Mem.exchange (xin : [[x : τ ∈ Γ₀, x' : τ', Γ₁, Γ₂]]) (wf : [[⊢ Γ₀, x' : τ', Γ₁, Γ₂]]) :
  [[x : τ ∈ Γ₀, Γ₁, x' : τ', Γ₂]] :=
  match append_elim xin with
  | .inl ⟨xin, xnin⟩ =>
    have ⟨xninΓ₁, xninΓ₂⟩ := NotMem.append.mp xnin
    match xin with
    | head => append_inl head xninΓ₂ |>.append_inr
    | ext xin xne => append_inl xin <| NotMem.append.mpr ⟨NotMem.ext.mpr ⟨xne, xninΓ₁⟩, xninΓ₂⟩
  | .inr xin => match append_elim xin with
    | .inl ⟨xinΓ₁, xninΓ₂⟩ => by
      if h : x = x' then
        subst x'
        rw [Environment.append_assoc] at wf
        have .ext _ xninΓ₀Γ₁ := wf.append_elim.left.exchange (Γ₂ := [[ε]])
        nomatch (NotMem.append.mp xninΓ₀Γ₁).right ⟨_, xinΓ₁⟩
      else
        exact .append_inr <| .append_inl (.ext ‹_› ‹_›) ‹_›
    | .inr xinΓ₂ => append_inr <| append_inr xinΓ₂

theorem NotMem.of_Mem_of_WellFormedness (xin : [[x : τ ∈ Γ₀]]) (wf : [[⊢ Γ₀, Γ₁]]) : [[x ∉ Γ₁]] :=
  match Γ₁, wf with
  | .empty, _ => nofun
  | .ext .., .ext wf x'nin =>
    ext.mpr ⟨
      fun | .refl .. => (append.mp x'nin).left ⟨_, xin⟩,
      of_Mem_of_WellFormedness xin wf
    ⟩

end Environment

namespace Term

namespace Typing

theorem toVarLocallyClosed : [[Γ ⊢ e : τ]] → e.VarLocallyClosed
  | var .. => .var_free
  | lam e'ty (I := I) =>
    have ⟨x, xnin⟩ := I.exists_fresh
    have e'ty := e'ty x xnin
    .lam <| e'ty.toVarLocallyClosed.weakening (.step .refl) |>.Var_open_drop <| Nat.zero_lt_succ _
  | app e₀ty e₁ty => .app e₀ty.toVarLocallyClosed e₁ty.toVarLocallyClosed
  | nat => .nat

theorem exchange : [[Γ₀, x : τ, Γ₁, Γ₂ ⊢ e : τ']] → [[Γ₀, Γ₁, x : τ, Γ₂ ⊢ e : τ']]
  | var wf x'in => var wf.exchange <| x'in.exchange wf
  | lam I e'ty => lam I (exchange (Γ₂ := .ext ..) <| e'ty · ·)
  | app e₀ty e₁ty => app e₀ty.exchange e₁ty.exchange
  | nat => nat

theorem weakening : [[Γ₀ ⊢ e : τ]] → [[⊢ Γ₀, Γ₁]] → [[Γ₀, Γ₁ ⊢ e : τ]]
  | var _ xin, wf =>
    var wf <| xin.append_inl <| Environment.NotMem.of_Mem_of_WellFormedness xin wf
  | lam I e'ty, wf =>
    lam ([[Γ₀, Γ₁]].dom ++ I) fun x xnin =>
      have ⟨xninΓ, xninI⟩ := List.not_mem_append'.mp xnin
      exchange (Γ₂ := [[ε]]) <| weakening (e'ty x xninI) <| wf.insert (xninΓ ·.choose_spec.dom)
  | app e₀ty e₁ty, wf => app (weakening e₀ty wf) (weakening e₁ty wf)
  | nat, _ => nat

theorem opening (e₁ty : Typing [[Γ₀, x : τ₀, Γ₁]] (Var_open e₁ x n) τ₁) (e₀ty : [[Γ₀ ⊢ e₀ : τ₀]])
  (xninΓ : [[x ∉ Γ₁]]) (xnine₁ : x ∉ freeVars e₁) : Typing [[Γ₀, Γ₁]] (e₁.Term_open e₀ n) τ₁ := by
  match e₁ with
  | .var (.free x') =>
    have .var Γwf x'in := e₁ty
    match x'in.append_elim with
    | .inl ⟨.head, x'nin⟩ => nomatch List.not_mem_singleton.mp xnine₁
    | .inl ⟨.ext x'in _, x'nin⟩ => exact .var Γwf.drop <| x'in.append_inl x'nin
    | .inr x'in => exact .var Γwf.drop x'in.append_inr
  | .var (.bound _) =>
    rw [Term.Var_open] at e₁ty
    split at e₁ty
    case isFalse => nomatch e₁ty
    case isTrue eq =>
    cases eq
    simp [Term.Term_open]
    have .var Γwf xin := e₁ty
    match xin.append_elim with
    | .inl ⟨.head, _⟩ => exact weakening e₀ty Γwf.drop
    | .inr xin => nomatch xninΓ ⟨_, xin⟩
  | [[λ x. e₁']] =>
    have .lam I e₁'ty := e₁ty
    apply lam <| x :: I
    intro x' x'nin
    have ⟨xne, x'ninI⟩ := List.not_mem_cons.mp x'nin
    symm at xne
    specialize e₁'ty x' x'ninI
    rw [e₀ty.toVarLocallyClosed.Var_open_Term_open_comm <| Nat.succ_ne_zero _]
    rw [e₁'.Var_open_comm <| Nat.succ_ne_zero _] at e₁'ty
    exact e₁'ty.opening (Γ₁ := .ext ..) e₀ty (Environment.NotMem.ext.mpr ⟨xne, xninΓ⟩) <|
      not_mem_freeVars_Var_open_intro xnine₁ xne
  | [[e₁₀ e₁₁]] =>
    have .app e₁₀ty e₁₁ty := e₁ty
    cases List.not_mem_append'.mp xnine₁
    apply app (opening e₁₀ty ..) (opening e₁₁ty ..) <;> assumption
  | [[n]] =>
    have .nat := e₁ty
    exact nat

end Typing

namespace Reduction

theorem preservation : [[e → e']] → [[Γ ⊢ e : τ]] → [[Γ ⊢ e' : τ]]
  | appl h, .app e₀ty e₁ty => .app (preservation h e₀ty) e₁ty
  | appr h, .app e₀ty e₁ty => .app e₀ty <| preservation h e₁ty
  | lamApp, .app (.lam I e₀'ty (e := e₀')) vty =>
    have ⟨x, xnin⟩ := freeVars e₀' ++ I |>.exists_fresh
    have ⟨xninfve₀', xninI⟩ := List.not_mem_append'.mp xnin
    e₀'ty x xninI |>.opening (Γ₁ := [[ε]]) vty nofun xninfve₀'

theorem progress : {e : Term} → [[ε ⊢ e : τ]] → IsValue e ∨ ∃ e', [[e → e']]
  | [[λ x. e₀]], _ => .inl .lam
  | [[e₀ e₁]], .app e₀ty e₁ty => match progress e₀ty with
    | .inl .lam => match progress e₁ty with
      | .inl e₁IsValue => .inr ⟨_, lamApp (v := ⟨_, e₁IsValue⟩)⟩
      | .inr ⟨_, h⟩ => .inr ⟨_, appr h (v := ⟨_, .lam⟩)⟩
    | .inr ⟨_, h⟩ => .inr ⟨_, appl h⟩
  | [[n]], .nat => .inl .nat

end Reduction

end Term

end LottExamples.STLC
