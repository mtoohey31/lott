import Lott
import Lott.Data.List
import Lott.DSL.Elab.UniversalJudgement

namespace LottExamples.STLC

nonterminal Type', τ :=
  | τ₀ " → " τ₁ : arr

locally_nameless
metavar Var, x

judgement_syntax x " ≠ " x' : VarId.Ne (id x, x')

abbrev VarId.Ne (x x' : VarId) := x ≠ x'

nonterminal Term, e :=
  | x             : var
  | "λ " x ". " e : lam (bind x in e)
  | e₀ e₁         : app
  | "(" e ")"     : paren (desugar := return e)

namespace Term

@[simp]
theorem Var_open_sizeOf (e : Term) : sizeOf (e.Var_open x n) = sizeOf e := by
  have : ∀ e : Term, e._sizeOf_1 = sizeOf e := fun _ => by dsimp only [sizeOf]
  match e with
  | var (.free _) => rw [Var_open, if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [Var_open]
    split
    · case isTrue h =>
      dsimp only [sizeOf]
      rw [_sizeOf_1, _sizeOf_1]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse h => rfl
  | lam e' =>
    dsimp only [sizeOf]
    rw [Var_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, this, this, e'.Var_open_sizeOf (n := n + 1)]
  | app e₀ e₁ =>
    dsimp only [sizeOf]
    rw [Var_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, this, this, this, this,
        e₀.Var_open_sizeOf, e₁.Var_open_sizeOf]

theorem Var_open_comm (e : Term) (mnen : m ≠ n)
  : (e.Var_open x m).Var_open x' n = (e.Var_open x' n).Var_open x m := by match e with
  | var (.free _) => simp [Var_open]
  | var (.bound _) =>
    rw [Var_open]
    split
    · case isTrue h =>
      cases h
      rw [Var_open, if_neg (nomatch ·), Var_open, if_neg (mnen.symm <| Var.bound.inj ·), Var_open,
          if_pos rfl]
    · case isFalse h =>
      rw [Var_open]
      split
      · case isTrue h' =>
        cases h'
        rw [Var_open, if_neg (nomatch ·)]
      · case isFalse h' => rw [Var_open, if_neg h]
  | lam e' => simp [Var_open, e'.Var_open_comm (mnen <| Nat.succ_inj'.mp ·)]
  | app e₀ e₁ => simp [Var_open, e₀.Var_open_comm mnen, e₁.Var_open_comm mnen]

namespace VarLocallyClosed

theorem weakening (e : Term) (mlen : m ≤ n) : e.VarLocallyClosed m → e.VarLocallyClosed n
  | var_free => var_free
  | var_bound h => var_bound <| Nat.lt_of_lt_of_le h mlen
  | lam e'lc => lam <| e'lc.weakening <| Nat.succ_le_succ_iff.mpr mlen
  | app e₀lc e₁lc => app (e₀lc.weakening mlen) (e₁lc.weakening mlen)

theorem Var_open_drop (e : Term) (mltn : m < n)
  : (e.Var_open x m).VarLocallyClosed n → e.VarLocallyClosed n := fun eoplc => by match e with
  | var (.free _) => exact var_free
  | var (.bound _) =>
    rw [Var_open] at eoplc
    split at eoplc
    · case isTrue h =>
      cases h
      exact var_bound mltn
    · case isFalse h => exact eoplc
  | .lam e' =>
    rw [Var_open] at eoplc
    simp only at eoplc
    let .lam e'oplc := eoplc
    exact lam <| e'oplc.Var_open_drop <| Nat.succ_lt_succ_iff.mpr mltn
  | .app e₀ e₁ =>
    rw [Var_open] at eoplc
    let .app e₀oplc e₁oplc := eoplc
    exact app (e₀oplc.Var_open_drop mltn) (e₁oplc.Var_open_drop mltn)

theorem Var_open_eq_of (e : Term) (elc : e.VarLocallyClosed n) : e.Var_open x n = e := by
  match e with
  | var (.free _) => simp [Var_open]
  | var (.bound _) =>
    rw [Var_open]
    split
    · case isTrue h =>
      cases h
      let .var_bound nltn := elc
      nomatch Nat.ne_of_lt nltn
    · case isFalse h => rfl
  | .lam e' =>
    let .lam e'lc := elc
    simp [Var_open, e'lc.Var_open_eq_of]
  | .app e₀ e₁ =>
    let .app e₀lc e₁lc := elc
    simp [Var_open, e₀lc.Var_open_eq_of, e₁lc.Var_open_eq_of]

theorem Var_open_Term_open_comm {e e' : Term} (e'lc : e'.VarLocallyClosed) (mnen : m ≠ n)
  : (e.Term_open e' m).Var_open x n = (e.Var_open x n).Term_open e' m := by match e with
  | var (.free _) => simp [Var_open, Term_open]
  | var (.bound _) =>
    rw [Term_open]
    split
    · case isTrue h =>
      cases h
      rw [Var_open, if_neg (mnen.symm <| Var.bound.inj ·), Term_open, if_pos rfl,
          e'lc.weakening (Nat.zero_le _) |>.Var_open_eq_of]
    · case isFalse h =>
      rw [Var_open]
      split
      · case isTrue h' =>
        cases h'
        rw [Term_open, if_neg (nomatch ·)]
      · case isFalse h' => rw [Term_open, if_neg h]
  | .lam e' =>
    rw [Term_open, Var_open, Var_open, Term_open]
    simp only
    rw [e'lc.Var_open_Term_open_comm]
    exact (mnen <| Nat.succ_inj'.mp ·)
  | .app e₀ e₁ =>
    simp [Term_open, Var_open, e'lc.Var_open_Term_open_comm mnen, e'lc.Var_open_Term_open_comm mnen]

end VarLocallyClosed

end Term

judgement_syntax x " ∈ " "fv" "(" e ")" : Term.InFreeVars (id x)

namespace Term.InFreeVars

theorem exists_gt (e : Term) : ∃ x : Nat, ∀ x' : Nat, [[x' ∈ fv(e)]] → x' < x :=
  match e with
  | .var (.free (x : Nat)) => .intro (x + 1) fun | _, var => Nat.lt_succ_self _
  | .var (.bound _) => .intro 0 fun _ => (nomatch ·)
  | .lam e' =>
    let ⟨xe', xe'gt⟩ := exists_gt e'
    .intro xe' fun | _, lam x'infve' => xe'gt _ x'infve'
  | .app e₀ e₁ =>
    let ⟨xe₀, xe₀gt⟩ := exists_gt e₀
    let ⟨xe₁, xe₁gt⟩ := exists_gt e₁
    .intro (max xe₀ xe₁) fun
      | _, app₀ x'infve₀ => Nat.lt_of_lt_of_le (xe₀gt _ x'infve₀) <| Nat.le_max_left _ _
      | _, app₁ x'infve₁ => Nat.lt_of_lt_of_le (xe₁gt _ x'infve₁) <| Nat.le_max_right _ _

theorem Var_open : InFreeVars x (e.Var_open x' n) → x ≠ x' → [[x ∈ fv(e)]] :=
  fun xinfveop xnex' => by match e with
    | .var (.free _) =>
      rw [Term.Var_open, if_neg (nomatch ·)] at xinfveop
      let .var := xinfveop
      exact var
    | .var (.bound _) =>
      rw [Term.Var_open] at xinfveop
      split at xinfveop
      · case isTrue h =>
        cases h
        let .var := xinfveop
        exact xnex' rfl |>.elim
      · case isFalse h => exact xinfveop
    | .lam e' =>
      rw [Term.Var_open] at xinfveop
      simp only at xinfveop
      let .lam xinfve'op := xinfveop
      exact lam <| xinfve'op.Var_open xnex'
    | .app e₀ e₁ =>
      rw [Term.Var_open] at xinfveop
      match xinfveop with
      | app₀ xinfve₀op => exact app₀ <| xinfve₀op.Var_open xnex'
      | app₁ xinfve₁op => exact app₁ <| xinfve₁op.Var_open xnex'


end Term.InFreeVars

judgement_syntax x " ∉ " "fv" "(" e ")" : Term.NotInFreeVars (id x)

abbrev Term.NotInFreeVars x e := ¬[[x ∈ fv(e)]]

namespace Term.NotInFreeVars

theorem exists_fresh (e : Term) (I : List VarId) : ∃ x ∉ I, [[x ∉ fv(e)]] :=
  let ⟨xI, xIgt⟩ := I.exists_gt
  let ⟨xE, xEgt⟩ := InFreeVars.exists_gt e
  let xIE := max xI xE
  .intro xIE ⟨
    fun inI => Nat.not_le_of_lt (xIgt xIE inI) <| Nat.le_max_left _ _,
    fun inE => Nat.not_le_of_lt (xEgt xIE inE) <| Nat.le_max_right _ _
  ⟩

theorem lam : [[x ∉ fv(λ x. e)]] → [[x ∉ fv(e)]] := (· <| .lam ·)

theorem app₀ : [[x ∉ fv(e₀ e₁)]] → [[x ∉ fv(e₀)]] := (· <| .app₀ ·)

theorem app₁ : [[x ∉ fv(e₀ e₁)]] → [[x ∉ fv(e₁)]] := (· <| .app₁ ·)

theorem Var_open : [[x ∉ fv(e)]] → x ≠ x' → [[x ∉ fv(e^x')]] :=
  fun xninfve xnex' xinfveop => xninfve <| xinfveop.Var_open xnex'

end Term.NotInFreeVars

private
def Environment.appendExpr : Lean.Expr := .const `LottExamples.STLC.Environment.append []

nonterminal Environment, Γ :=
  | "ε"              : empty
  | Γ ", " x " : " τ : ext (id x)
  | Γ₀ ", " Γ₁       : append (elab := return Lean.mkApp2 Environment.appendExpr Γ₀ Γ₁)

namespace Environment

def append (Γ₀ : Environment) : Environment → Environment
  | empty => Γ₀
  | ext Γ₁ x τ => Γ₀.append Γ₁ |>.ext x τ

def empty_append (Γ : Environment) : Environment.empty.append Γ = Γ := match Γ with
  | empty => rfl
  | ext Γ' x τ => by rw [append, Γ'.empty_append]

def append_assoc {Γ₀ : Environment} : Γ₀.append (Γ₁.append Γ₂) = (Γ₀.append Γ₁).append Γ₂ := by
  match Γ₂ with
  | empty => rfl
  | ext Γ₂' x τ => rw [append, append, append_assoc, ← append]

end Environment

judgement_syntax x " : " τ " ∈ " Γ : Environment.VarIn (id x)

judgement Environment.VarIn :=

──────────────── head
x : τ ∈ Γ, x : τ

x : τ ∈ Γ
x ≠ x'
────────────────── ext
x : τ ∈ Γ, x' : τ'

judgement_syntax x " ∉ " Γ : Environment.VarNotIn (id x)

def Environment.VarNotIn x Γ := ∀ τ, ¬[[x : τ ∈ Γ]]

namespace Environment

theorem VarNotIn.ext : [[x ∉ Γ, x' : τ]] ↔ x ≠ x' ∧ [[x ∉ Γ]] where
  mp xninΓx' := ⟨
    fun | .refl .. => xninΓx' _ .head,
    fun _ xinΓ => Classical.byCases
      fun | .refl .. => xninΓx' _ .head
      fun xnex' => xninΓx' _ <| xinΓ.ext xnex'
  ⟩
  mpr
    | ⟨xnex', _⟩, _, .head => nomatch xnex'
    | ⟨_, xninΓ⟩, _, .ext xinΓ _ => xninΓ _ xinΓ

namespace VarIn

theorem append_elim : [[x : τ ∈ Γ₀, Γ₁]] → [[x : τ ∈ Γ₀]] ∧ [[x ∉ Γ₁]] ∨ [[x : τ ∈ Γ₁]] :=
  fun xinΓ₀Γ₁ => match Γ₁ with
    | .empty => .inl ⟨xinΓ₀Γ₁, fun _ => (nomatch ·)⟩
    | .ext .. =>
      match xinΓ₀Γ₁ with
      | head => .inr head
      | ext xinΓ₀Γ₁' xnex' => match xinΓ₀Γ₁'.append_elim with
        | .inl ⟨xinΓ₀, xninΓ₁'⟩ => .inl ⟨xinΓ₀, VarNotIn.ext.mpr ⟨xnex', xninΓ₁'⟩⟩
        | .inr xinΓ₁' => .inr <| xinΓ₁'.ext xnex'

theorem append_inl : [[x : τ ∈ Γ₀]] → [[x ∉ Γ₁]] → [[x : τ ∈ Γ₀, Γ₁]] :=
  fun xinΓ₀ xninΓ₁ => match Γ₁ with
    | .empty => xinΓ₀
    | .ext .. =>
      let ⟨xnex', xninΓ₁'⟩ := VarNotIn.ext.mp xninΓ₁
      xinΓ₀.append_inl xninΓ₁' |>.ext xnex'

theorem append_inr : [[x : τ ∈ Γ₁]] → [[x : τ ∈ Γ₀, Γ₁]]
  | head => head
  | ext xinΓ₁' xnex' => xinΓ₁'.append_inr.ext xnex'

end VarIn

theorem VarNotIn.append : [[x ∉ Γ₀, Γ₁]] ↔ [[x ∉ Γ₀]] ∧ [[x ∉ Γ₁]] where
  mp xninΓ₀Γ₁ := ⟨
    fun _ xinΓ₀ => Classical.byCases (p := ∃ τ, [[x : τ ∈ Γ₁]])
      (fun ⟨_, xinΓ₁⟩ => xninΓ₀Γ₁ _ xinΓ₁.append_inr)
      fun xninΓ₁ => xninΓ₀Γ₁ _ <| xinΓ₀.append_inl <| not_exists.mp xninΓ₁,
    fun _ => (xninΓ₀Γ₁ _ ·.append_inr)
  ⟩
  mpr | ⟨xninΓ₀, xninΓ₁⟩, _, xinΓ₀Γ₁ => match xinΓ₀Γ₁.append_elim with
    | .inl ⟨xinΓ₀, _⟩ => xninΓ₀ _ xinΓ₀
    | .inr xinΓ₁ => xninΓ₁ _ xinΓ₁

def domain : Environment → List VarId
  | empty => []
  | ext Γ x _ => x :: Γ.domain

end Environment

judgement_syntax x " ∈ " "dom" "(" Γ ")" : Environment.VarInDom (id x)

abbrev Environment.VarInDom x (Γ : Environment) := x ∈ Γ.domain

namespace Environment.VarInDom

theorem insert : [[x ∈ dom(Γ₀, Γ₁)]] → [[x ∈ dom(Γ₀, x' : τ, Γ₁)]] :=
  fun xindomΓ₀Γ₁ =>
    match Γ₁ with
    | .empty => .tail _ xindomΓ₀Γ₁
    | .ext .. => match xindomΓ₀Γ₁ with
      | .head _ => .head _
      | .tail _ xindomΓ₀Γ₁' => .tail _ <| insert xindomΓ₀Γ₁'

theorem of_VarIn : [[x : τ ∈ Γ]] → [[x ∈ dom(Γ)]]
  | .head => .head _
  | .ext xinΓ' _ => .tail _ <| of_VarIn xinΓ'

theorem append_elim : [[x ∈ dom(Γ₀, Γ₁)]] → [[x ∈ dom(Γ₀)]] ∨ [[x ∈ dom(Γ₁)]] := fun xindomΓ₀Γ₁ =>
  match Γ₁ with
  | .empty => .inl xindomΓ₀Γ₁
  | .ext .. => match xindomΓ₀Γ₁ with
    | .head _ => .inr <| .head _
    | .tail _ xindomΓ₀Γ₁' => match append_elim xindomΓ₀Γ₁' with
      | .inl xindomΓ₀ => .inl xindomΓ₀
      | .inr xindomΓ₁' => .inr <| .tail _ <| xindomΓ₁'

theorem append_inl : [[x ∈ dom(Γ₀)]] → [[x ∈ dom(Γ₀, Γ₁)]] := fun xindomΓ₀ => match Γ₁ with
  | .empty => xindomΓ₀
  | .ext .. => .tail _ xindomΓ₀.append_inl

theorem append_inr : [[x ∈ dom(Γ₁)]] → [[x ∈ dom(Γ₀, Γ₁)]] := fun xindomΓ₁ =>
  let .ext .. := Γ₁
  match xindomΓ₁ with
  | .head _ => .head _
  | .tail _ xinΓ₁' => .tail _ <| append_inr xinΓ₁'

end Environment.VarInDom

judgement_syntax x " ∉ " "dom" "(" Γ ")" : Environment.VarNotInDom (id x)

def Environment.VarNotInDom x Γ := ¬[[x ∈ dom(Γ)]]

namespace Environment.VarNotInDom

theorem drop : [[x ∉ dom(Γ₀, x' : τ, Γ₁)]] → [[x ∉ dom(Γ₀, Γ₁)]] :=
  (· ·.insert)

theorem append : [[x ∉ dom(Γ₀, Γ₁)]] ↔ [[x ∉ dom(Γ₀)]] ∧ [[x ∉ dom(Γ₁)]] where
  mp xnindomΓ₀Γ₁ := ⟨(xnindomΓ₀Γ₁ ·.append_inl), (xnindomΓ₀Γ₁ ·.append_inr)⟩
  mpr | ⟨xnindomΓ₀, xnindomΓ₁⟩, xindomΓ₀Γ₁ => match xindomΓ₀Γ₁.append_elim with
    | .inl xindomΓ₀ => xnindomΓ₀ xindomΓ₀
    | .inr xindomΓ₁ => xnindomΓ₁ xindomΓ₁

theorem ext : [[x ∉ dom(Γ, x' : τ)]] ↔ x ≠ x' ∧ [[x ∉ dom(Γ)]] where
  mp xnindomΓx' := ⟨
    fun | .refl .. => xnindomΓx' <| .head _,
    (xnindomΓx' <| .tail _ ·)
  ⟩
  mpr | ⟨xnex', xnindomΓ⟩, xindomΓx' => match xindomΓx' with
    | .head _ => nomatch xnex'
    | .tail _ xindomΓ => xnindomΓ xindomΓ

theorem exchange : [[x ∉ dom(Γ₀, x' : τ, Γ₁, Γ₂)]] → [[x ∉ dom(Γ₀, Γ₁, x' : τ, Γ₂)]] :=
  fun xnindomΓ₀x'Γ₁Γ₂ =>
    let ⟨xnindomΓ₀x', xnindomΓ₁Γ₂⟩ := append.mp xnindomΓ₀x'Γ₁Γ₂
    let ⟨xnex', xnindomΓ₀⟩ := ext.mp xnindomΓ₀x'
    let ⟨xnindomΓ₁, xnindomΓ₂⟩ := append.mp xnindomΓ₁Γ₂
    append.mpr ⟨xnindomΓ₀, append.mpr ⟨ext.mpr ⟨xnex', xnindomΓ₁⟩, xnindomΓ₂⟩⟩

end Environment.VarNotInDom

judgement_syntax "⊢ " Γ : Environment.WellFormedness

judgement Environment.WellFormedness :=

─── empty
⊢ ε

⊢ Γ
x ∉ dom(Γ)
────────── ext
⊢ Γ, x : τ

namespace Environment

namespace WellFormedness

theorem insert : [[⊢ Γ₀, Γ₁]] → [[x ∉ dom(Γ₀, Γ₁)]] → [[⊢ Γ₀, x : τ, Γ₁]] :=
  fun Γ₀Γ₁wf xnindomΓ₀Γ₁ => by match Γ₁ with
    | .empty => exact Γ₀Γ₁wf.ext xnindomΓ₀Γ₁
    | .ext Γ₁' x' τ' =>
      let .ext Γ₀Γ₁'wf x'nindomΓ₀Γ₁' := Γ₀Γ₁wf
      let ⟨x'nindomΓ₀, x'nindomΓ₁'⟩ := VarNotInDom.append.mp x'nindomΓ₀Γ₁'
      let ⟨_, xnindomΓ₁⟩  := VarNotInDom.append.mp xnindomΓ₀Γ₁
      let x'nindom : [[x' ∉ dom(Γ₀, x : τ, Γ₁')]] := VarNotInDom.append.mpr
        ⟨VarNotInDom.ext.mpr ⟨VarNotInDom.ext.mp xnindomΓ₁ |>.left.symm, x'nindomΓ₀⟩, x'nindomΓ₁'⟩
      exact Γ₀Γ₁'wf.insert (VarNotInDom.ext.mp xnindomΓ₀Γ₁).right |>.ext x'nindom

theorem drop : [[⊢ Γ₀, x : τ, Γ₁]] → [[⊢ Γ₀, Γ₁]] :=
  fun Γ₀xΓ₁wf => match Γ₁ with
    | .empty =>
      let .ext Γ₀wf _ := Γ₀xΓ₁wf
      Γ₀wf
    | .ext .. =>
      let .ext Γ₀xΓ₁'wf xnindomΓ₀xΓ₁' := Γ₀xΓ₁wf
      Γ₀xΓ₁'wf.drop.ext xnindomΓ₀xΓ₁'.drop

theorem exchange : [[⊢ Γ₀, x : τ, Γ₁, Γ₂]] → [[⊢ Γ₀, Γ₁, x : τ, Γ₂]] := fun Γ₀xΓ₁Γ₂wf =>
  match Γ₂ with
  | .empty => by induction Γ₁ with
    | empty => exact Γ₀xΓ₁Γ₂wf
    | ext Γ₁' x' τ' ih =>
      simp [append] at Γ₀xΓ₁Γ₂wf ih ⊢
      let .ext Γ₀xΓ₁'wf x'nindomΓ₀xΓ₁' := Γ₀xΓ₁Γ₂wf
      let .ext Γ₀Γ₁'wf xnindomΓ₀Γ₁ := ih Γ₀xΓ₁'wf
      let ⟨x'nindomΓ₀x, _⟩ := VarNotInDom.append.mp x'nindomΓ₀xΓ₁'
      let ⟨xnex', _⟩ := VarNotInDom.ext.mp x'nindomΓ₀x
      exact Γ₀Γ₁'wf.ext x'nindomΓ₀xΓ₁'.drop |>.ext <| VarNotInDom.ext.mpr ⟨xnex'.symm, xnindomΓ₀Γ₁⟩
  | .ext Γ₂' x' τ' =>
    let .ext Γ₀xΓ₁Γ₂'wf x'ninΓ₀xΓ₁Γ₂' := Γ₀xΓ₁Γ₂wf
    Γ₀xΓ₁Γ₂'wf.exchange.ext x'ninΓ₀xΓ₁Γ₂'.exchange

end WellFormedness

theorem VarIn.exchange
  : [[x : τ ∈ Γ₀, x' : τ', Γ₁, Γ₂]] → [[⊢ Γ₀, x' : τ', Γ₁, Γ₂]] → [[x : τ ∈ Γ₀, Γ₁, x' : τ', Γ₂]] :=
  fun xinΓ₀x'Γ₁Γ₂ Γ₀x'Γ₁Γ₂wf =>
    match xinΓ₀x'Γ₁Γ₂.append_elim with
    | .inl ⟨xinΓ₀x', xninΓ₁Γ₂⟩ =>
      let ⟨xninΓ₁, xninΓ₂⟩ := VarNotIn.append.mp xninΓ₁Γ₂
      match xinΓ₀x' with
      | .head => VarIn.head.append_inl xninΓ₂ |>.append_inr
      | .ext xinΓ₀ xnex' =>
        xinΓ₀.append_inl <| VarNotIn.append.mpr ⟨VarNotIn.ext.mpr ⟨xnex', xninΓ₁⟩, xninΓ₂⟩
    | .inr xinΓ₁Γ₂ => match xinΓ₁Γ₂.append_elim with
      | .inl ⟨xinΓ₁, xninΓ₂⟩ =>
        let f xeqx' :=
          let .refl _ := xeqx'
          let .refl _ : τ = τ' := by
            rw [Environment.append_assoc] at Γ₀x'Γ₁Γ₂wf
            induction Γ₂ with
            | empty =>
              simp [Environment.append] at *
              induction Γ₁ with
              | empty => nomatch xinΓ₁
              | ext Γ₁' x'' τ'' ih =>
                let .ext Γ₀xΓ₁'wf x'''nindomΓ₀xΓ₁' := Γ₀x'Γ₁Γ₂wf
                match xinΓ₁ with
                | .head =>
                  let ⟨x''nindomΓ₀x, _⟩ := VarNotInDom.append.mp x'''nindomΓ₀xΓ₁'
                  nomatch VarNotInDom.ext.mp x''nindomΓ₀x
                | .ext xinΓ₁' xnex'' =>
                  match xinΓ₀x'Γ₁Γ₂ with
                  | .head => nomatch xnex''
                  | .ext xinΓ₀xΓ₁' _ => exact ih xinΓ₁' xinΓ₁' xinΓ₀xΓ₁' Γ₀xΓ₁'wf
            | ext Γ₂' x'' τ'' ih =>
              match xinΓ₁Γ₂ with
              | .head => exact xninΓ₂ _ .head |>.elim
              | .ext xinΓ₁Γ₂' xnex'' =>
                let ⟨_, xninΓ₂'⟩ := VarNotIn.ext.mp xninΓ₂
                match xinΓ₀x'Γ₁Γ₂ with
                | .head => nomatch xnex''
                | .ext xinΓ₀x'Γ₁Γ₂' _ =>
                  let .ext Γ₀x'Γ₁Γ₂'wf _ := Γ₀x'Γ₁Γ₂wf
                  exact ih xinΓ₁Γ₂' xninΓ₂' xinΓ₀x'Γ₁Γ₂' Γ₀x'Γ₁Γ₂'wf
          VarIn.head.append_inl xninΓ₂
        Classical.byCases (p := x = x') f (xinΓ₁.ext · |>.append_inl xninΓ₂) |>.append_inr
      | .inr xinΓ₂ => xinΓ₂.append_inr.append_inr

theorem VarNotIn.of_VarIn_of_WellFormedness
  : [[x : τ ∈ Γ₀]] → [[⊢ Γ₀, Γ₁]] → [[x ∉ Γ₁]] := fun xinΓ₀ Γ₀Γ₁wf => match Γ₁ with
  | .empty => fun _ => (nomatch ·)
  | .ext .. =>
    let .ext Γ₀Γ₁'wf x'ninΓ₀Γ₁ := Γ₀Γ₁wf
    ext.mpr ⟨
      fun | .refl .. => (VarNotInDom.append.mp x'ninΓ₀Γ₁).left <| VarInDom.of_VarIn xinΓ₀,
      of_VarIn_of_WellFormedness xinΓ₀ Γ₀Γ₁'wf
    ⟩

end Environment

judgement_syntax Γ " ⊢ " e " : " τ : Typing

judgement Typing :=

⊢ Γ
x : τ ∈ Γ
───────── var
Γ ⊢ x : τ

∀ x ∉ (I : List _), Γ, x : τ₀ ⊢ e^x : τ₁
──────────────────────────────────────── lam
Γ ⊢ λ x. e : τ₀ → τ₁

Γ ⊢ e₀ : τ₀ → τ₁
Γ ⊢ e₁ : τ₀
──────────────── app
Γ ⊢ e₀ e₁ : τ₁

namespace Typing

theorem toVarLocallyClosed : [[Γ ⊢ e : τ]] → e.VarLocallyClosed
  | var .. => .var_free
  | lam e'ty (I := I) =>
    let ⟨x, xnin⟩ := I.exists_fresh
    let e'ty := e'ty x xnin
    .lam <| e'ty.toVarLocallyClosed.weakening (Nat.le_succ 0) |>.Var_open_drop <| Nat.zero_lt_succ _
  | app e₀ty e₁ty => .app e₀ty.toVarLocallyClosed e₁ty.toVarLocallyClosed

theorem exchange : [[Γ₀, x : τ, Γ₁, Γ₂ ⊢ e : τ']] → [[Γ₀, Γ₁, x : τ, Γ₂ ⊢ e : τ']]
  | var Γ₀xΓ₁Γ₂wf x'inΓ₀xΓ₁Γ₂ => var Γ₀xΓ₁Γ₂wf.exchange <| x'inΓ₀xΓ₁Γ₂.exchange Γ₀xΓ₁Γ₂wf
  | lam e'ty => lam fun x' x'nin => let e'ty := e'ty x' x'nin; e'ty.exchange (Γ₂ := Γ₂.ext x' _)
  | app e₀ty e₁ty => app e₀ty.exchange e₁ty.exchange

theorem weakening : [[Γ₀ ⊢ e : τ]] → [[⊢ Γ₀, Γ₁]] → [[Γ₀, Γ₁ ⊢ e : τ]]
  | var _ xinΓ₀, Γ₀Γ₁wf =>
    var Γ₀Γ₁wf <| xinΓ₀.append_inl <| Environment.VarNotIn.of_VarIn_of_WellFormedness xinΓ₀ Γ₀Γ₁wf
  | lam e'ty (I := I), Γ₀Γ₁wf =>
    lam (I := (Γ₀.append Γ₁).domain ++ I) fun x xnin => by
      let ⟨xnindomΓ₀Γ₁, xninI⟩ := List.not_mem_append'.mp xnin
      let e'ty := e'ty x xninI
      have := e'ty.weakening (Γ₀Γ₁wf.insert xnindomΓ₀Γ₁)
      exact this.exchange (Γ₂ := .empty)
  | app e₀ty e₁ty, Γ₀Γ₁wf => app (e₀ty.weakening Γ₀Γ₁wf) (e₁ty.weakening Γ₀Γ₁wf)

theorem opening
  (e₁ty : Typing ((Γ₀.ext x τ₀).append Γ₁) (e₁.Var_open x n) τ₁) (e₀ty : [[Γ₀ ⊢ e₀ : τ₀]])
  (xninΓ₁ : [[x ∉ Γ₁]]) (xninfve₁ : [[x ∉ fv(e₁)]])
  : Typing (Γ₀.append Γ₁) (e₁.Term_open e₀ n) τ₁ := by
  match e₁ with
  | .var (.free x') =>
    rw [Term.Var_open, if_neg (nomatch ·)] at e₁ty
    let .var Γ₀xΓ₁wf x'inΓ₀xΓ₁ := e₁ty
    match x'inΓ₀xΓ₁.append_elim with
    | .inl ⟨.head, x'ninΓ₁⟩ => exact xninfve₁ .var |>.elim
    | .inl ⟨.ext x'inΓ₀ _, x'ninΓ₁⟩ => exact .var Γ₀xΓ₁wf.drop <| x'inΓ₀.append_inl x'ninΓ₁
    | .inr x'inΓ₁ => exact .var Γ₀xΓ₁wf.drop x'inΓ₁.append_inr
  | .var (.bound _) =>
    rw [Term.Var_open] at e₁ty
    split at e₁ty
    · case isTrue h =>
      cases h
      rw [Term.Term_open, if_pos rfl]
      let .var Γ₀xΓ₁wf xinΓ₀xΓ₁ := e₁ty
      match xinΓ₀xΓ₁.append_elim with
      | .inl ⟨.head, _⟩ => exact e₀ty.weakening Γ₀xΓ₁wf.drop
      | .inr xinΓ₁ => exact xninΓ₁ _ xinΓ₁ |>.elim
    · case isFalse h => nomatch e₁ty
  | .lam e₁' =>
    rw [Term.Term_open]
    let .lam e₁'ty (τ₀ := τ₀') (I := I) := e₁ty
    exact .lam (I := x :: I) fun x' x'nin => by
      let xnex' := List.ne_of_not_mem_cons x'nin
      let e₁'ty := e₁'ty x' <| List.not_mem_of_not_mem_cons x'nin
      have : ((Γ₀.ext x τ₀).append Γ₁).ext x' τ₀' = (Γ₀.ext x τ₀).append (Γ₁.ext x' τ₀') := rfl
      rw [this, e₁'.Var_open_comm <| Nat.succ_ne_zero _] at e₁'ty
      rw [e₀ty.toVarLocallyClosed.Var_open_Term_open_comm <| Nat.succ_ne_zero _]
      let xninΓ₁x' : [[x ∉ Γ₁, x' : τ₀']] := Environment.VarNotIn.ext.mpr ⟨xnex'.symm, xninΓ₁⟩
      exact e₁'ty.opening e₀ty xninΓ₁x' <| xninfve₁.lam.Var_open xnex'.symm
  | .app e₁₀ e₁₁ =>
    let .app e₁₀ty e₁₁ty := e₁ty
    exact .app (e₁₀ty.opening e₀ty xninΓ₁ xninfve₁.app₀) (e₁₁ty.opening e₀ty xninΓ₁ xninfve₁.app₁)

end Typing

nonterminal (parent := Term) Value, v :=
  | "λ " x ". " e : lam (bind x in e)

judgement_syntax e " ↦ " e' : Reduction

judgement Reduction :=

e₀ ↦ e₀'
────────────── appl
e₀ e₁ ↦ e₀' e₁

e₁ ↦ e₁'
────────────── appr
e₀ e₁ ↦ e₀ e₁'

───────────────── lamApp
(λ x. e) v ↦ e^^v

namespace Reduction

theorem preservation (ty : [[Γ ⊢ e : τ]]) (re : [[e ↦ e']]) : [[Γ ⊢ e' : τ]] := match re, ty with
  | appl e₀ree₀', .app e₀ty e₁ty => .app (e₀ree₀'.preservation e₀ty) e₁ty
  | appr e₁ree₁', .app e₀ty e₁ty => .app e₀ty <| e₁ree₁'.preservation e₁ty
  | lamApp, .app e₀ty vty =>
    let .lam e₀'ty (e := e₀') (I := I) := e₀ty
    let ⟨x, xninI, xninfve₀'⟩ := Term.NotInFreeVars.exists_fresh e₀' I
    e₀'ty x xninI |>.opening (Γ₁ := .empty) vty (fun _ => (nomatch ·)) xninfve₀'

theorem progress (ty : [[ε ⊢ e : τ]]) : e.IsValue ∨ ∃ e', [[e ↦ e']] := match e, ty with
  | .lam _, _ => .inl .lam
  | .app e₀ e₁, .app e₀ty e₁ty => match progress e₀ty with
    | .inl _ => match progress e₁ty with
      | .inl e₁IsValue =>
        let .lam _ := e₀
        let v₁ : Value := ⟨e₁, e₁IsValue⟩
        .inr <| .intro _ <| .lamApp (v := v₁)
      | .inr ⟨_, e₁ree₁'⟩ => .inr <| .intro _ <| .appr e₁ree₁'
    | .inr ⟨_, e₀ree₀'⟩ => .inr <| .intro _ <| .appl e₀ree₀'

end Reduction

end LottExamples.STLC
