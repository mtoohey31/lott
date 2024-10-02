import Lott

namespace LottExamples.SystemF

open Lean

metavar TypeVar, a, b
metavar TermVar, x, y

nonterminal Type', A, B :=
  | a                    : var
  | A " → " B            : arr
  | "∀ " a ". " A        : forall' (bind a in A)
  | "(" A ")"            : paren (desugar := return A)

theorem Type'.forall_subst_eq_subst_forall (aneb : a ≠ b)
  : [[∀ a. (A [B / b])]] = [[(∀ a. A) [B / b] ]] := by rw [Type'.TypeVar_subst, if_neg aneb.symm]

theorem Type'.subst_subst : [[(A' [A / a] [B / a])]] = [[(A' [A [B / a] / a])]] := by
  match A' with
  | .var a' =>
    rw [Type'.TypeVar_subst, Type'.TypeVar_subst]
    split
    · case isTrue a'eqa => rfl
    · case isFalse a'nea => rw [Type'.TypeVar_subst, if_neg a'nea]
  | .arr A' B' =>
    rw [Type'.TypeVar_subst, Type'.TypeVar_subst]
    rw [Type'.subst_subst, Type'.subst_subst]
    rw [← Type'.TypeVar_subst]
  | .forall' a' A' =>
    rw [Type'.TypeVar_subst, Type'.TypeVar_subst]
    split
    · case isTrue a'eqa => rw [Type'.TypeVar_subst, if_pos a'eqa]
    · case isFalse a'nea => rw [Type'.TypeVar_subst, Type'.subst_subst, if_neg a'nea]

theorem Type'.subst_shadowed_forall (B : Type') : [[∀ a. A]] = [[(∀ a. A) [B / a] ]] := by
  rw [Type'.TypeVar_subst, if_pos rfl]

nonterminal Term, E, F :=
  | x                     : var
  | "λ " x " : " A ". " E : lam (bind x in E)
  | E F                   : app
  | "Λ " a ". " E         : typeGen (bind a in E)
  | E " [" A "]"          : typeApp
  | "(" E ")"             : paren (desugar := return E)

nosubst
nonterminal Environment, G, D :=
  | "ε"                  : empty
  | G ", " x " : " A     : termVarExt
  | G ", " a             : typeVarExt
  | G ", " D             : append (elab := return mkAppN (.const `LottExamples.SystemF.Environment.append []) #[G, D])
  | "(" G ")"            : paren (desugar := return G)
  | G " [" A " / " a "]" : subst (elab := return mkAppN (.const `LottExamples.SystemF.Environment.subst []) #[G, a, A])

def Environment.append (G : Environment) : Environment → Environment
  | .empty => G
  | .termVarExt G' x A => G.append G' |>.termVarExt x A
  | .typeVarExt G' a => G.append G' |>.typeVarExt a

theorem Environment.empty_append (G : Environment) : G = Environment.empty.append G := by
  induction G with
  | empty => rfl
  | termVarExt G x A ih => congr
  | typeVarExt G a ih => congr

def Environment.subst (G : Environment) (a : TypeVar) (A : Type') : Environment :=
  go G |>.fst
where
  go
    | Environment.empty => (Environment.empty, false)
    | .termVarExt G' x A' =>
      let (G'', found) := go G'
      if found then
        (G''.termVarExt x A', true)
      else
        (G''.termVarExt x (A'.TypeVar_subst a A), false)
    | .typeVarExt G' a' =>
      let (G'', found) := go G'
      (G''.typeVarExt a', a' = a || found)

theorem Environment.subst_empty : Environment.empty = Environment.empty.subst a A := rfl

theorem Environment.subst_typeVarExt_eq_typeVarExt_subst
  : [[(G [B / b]), a]] = [[((G, a) [B / b])]] := rfl

nonterminal (parent := Term) Value, V :=
  | "λ " x " : " A ". " E : lam
  | "Λ " a ". " E         : typeGen

judgement_syntax a " ≠ " b : TypeVarNe

def TypeVarNe := Ne (α := TypeVar)

judgement_syntax a " ∈ " G : TypeVarInEnvironment

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

judgement_syntax a " ∉ " G : TypeVarNotInEnvironment

def TypeVarNotInEnvironment a G := ¬[[a ∈ G]]

theorem TypeVarInEnvironment.append_elim (ainGappGG : [[a ∈ G, GG]]) : [[a ∈ G]] ∨ [[a ∈ GG]] := by
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
        exact .head
      · case neg a'nea =>
        apply ih
        · cases ainGappGG
          · case ainGappGG.head => contradiction
          · case ainGappGG.typeVarExt => assumption
        · intro ainGG'
          apply aninGG
          have a'nea : a' ≠ a := a'nea
          exact ainGG'.typeVarExt a'nea.symm

theorem TypeVarInEnvironment.append_inl (ainG : [[a ∈ G]]) : [[a ∈ G, GG]] := by
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

theorem TypeVarInEnvironment.append_inr : [[a ∈ GG]] → [[a ∈ G, GG]]
  | .head => .head
  | .termVarExt ainGG' => ainGG'.append_inr |>.termVarExt
  | .typeVarExt ainGG' anea' => ainGG'.append_inr |>.typeVarExt anea'

theorem TypeVarInEnvironment.subst (ainG : [[a ∈ G]]) : [[a ∈ G [A / b] ]] := by
  rw [Environment.subst]
  induction G
  · case empty => cases ainG
  · case termVarExt G' x A' ih =>
    rw [Environment.subst.go]
    simp
    split <;>
    · simp
      apply TypeVarInEnvironment.termVarExt
      apply ih
      cases ainG
      case a.termVarExt ainG' =>
      exact ainG'
  · case typeVarExt G' a' ih =>
    rw [Environment.subst.go]
    simp
    cases ainG
    · case head => exact .head
    · case typeVarExt ainG' anea' =>
      apply TypeVarInEnvironment.typeVarExt _ anea'
      apply ih
      exact ainG'

theorem TypeVarNotInEnvironment.termVarExt (aninG : [[a ∉ G]]) : [[a ∉ G, x : A]] := by
  intro ainGx
  apply aninG
  cases ainGx
  case termVarExt ainG => exact ainG

theorem TypeVarNotInEnvironment.typeVarExt (aninG : [[a ∉ G]]) (bnea : b ≠ a) : [[a ∉ G, b]] := by
  intro ainGa
  apply aninG
  cases ainGa
  · case head => contradiction
  · case typeVarExt ainG _ => exact ainG

theorem TypeVarNotInEnvironment.TermVar_drop (aninGx : [[a ∉ G, x : A]]) : [[a ∉ G]] := by
  intro ainG
  exact aninGx ainG.termVarExt

theorem TypeVarNotInEnvironment.TypeVar_drop (aninGb : [[a ∉ G, b]]) : [[a ∉ G]] := by
  intro ainG
  by_cases a = b
  · case pos aeqb =>
    rw [aeqb] at aninGb
    exact aninGb .head
  · case neg aneb => exact aninGb <| ainG.typeVarExt aneb

theorem Environment.subst_go_snd_eq_false_of_TermVarNotInEnvironment G (aninG : [[a ∉ G]])
  : (Environment.subst.go a A G).snd = false := by
  cases G
  · case empty => rfl
  · case termVarExt G' x A' =>
    rw [subst.go]
    split
    split
    · case isTrue q r found receq foundeqtrue =>
      apply ne_false_of_eq_true (b := (subst.go a A G').snd)
      · simp [foundeqtrue, receq]
      · apply G'.subst_go_snd_eq_false_of_TermVarNotInEnvironment
        exact aninG.TermVar_drop
    · case isFalse => simp
  · case typeVarExt G' a' =>
    rw [subst.go]
    simp
    have a'nea : a' ≠ a := by
      intro a'eqa
      rw [a'eqa] at aninG
      apply aninG
      exact .head
    constructor
    · exact a'nea
    · apply G'.subst_go_snd_eq_false_of_TermVarNotInEnvironment
      exact aninG.TypeVar_drop

theorem Environment.subst_termVarExt_eq_termVarExt_subst_of_TypeVarNotInEnvironment
  (aninG : [[a ∉ G]]) : [[(G [B / a]), x : (A [B / a])]] = [[((G, x : A) [B / a])]] := by
  rw [Environment.subst, Environment.subst, subst.go]
  simp
  split
  · case isTrue sndeqtrue =>
    apply False.elim
    apply ne_false_of_eq_true sndeqtrue
    exact G.subst_go_snd_eq_false_of_TermVarNotInEnvironment aninG
  · case isFalse => simp

theorem TypeVarNotInEnvironment.ε : [[a ∉ ε]] := fun ainε => by cases ainε

judgement_syntax x " ≠ " y : TermVarNe

def TermVarNe := Ne (α := TermVar)

judgement_syntax x " : " A " ∈ " G : TermVarInEnvironment

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

judgement_syntax x " ∉ " G : TermVarNotInEnvironment

def TermVarNotInEnvironment x G := ∀ A : Type', ¬[[x : A ∈ G]]

theorem TermVarInEnvironment.append_elim (xAinGappGG : [[x : A ∈ G, GG]])
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
        cases xA'inε
    | .termVarExt GG' x' A' =>
      by_cases x' = x
      · case pos x'eqx =>
        by_cases A' = A
        · case pos A'eqA =>
          rw [x'eqx, A'eqA] at xAinGappGG xAninGG
          exact False.elim <| xAninGG .head
        · case neg A'neA =>
          cases xAinGappGG
          · case head => contradiction
          · case termVarExt xAinGappGG' xnex' =>
            exact False.elim <| xnex' x'eqx.symm
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
              | .head => contradiction
              | .termVarExt xA''inG'  _ => exact xninGG' A'' xA''inG'
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
        exact False.elim <| xAninGG xAinGG'.typeVarExt

theorem TermVarInEnvironment.append_inl (xAinG : [[x : A ∈ G]]) (xninGG : [[x ∉ GG]])
  : [[x : A ∈ G, GG]] := by
  match GG with
  | .empty => exact xAinG
  | .termVarExt GG' x' A' =>
    by_cases x' = x
    · case pos x'eqx =>
      rw [x'eqx]
      rw [x'eqx] at xninGG
      exact False.elim <| xninGG A' .head
    · case neg x'nex =>
      have x'nex : x' ≠ x := x'nex
      apply TermVarInEnvironment.termVarExt _ x'nex.symm
      apply xAinG.append_inl
      intro A'' xA''inGG'
      apply xninGG A''
      exact .termVarExt xA''inGG' x'nex.symm
  | .typeVarExt GG' a =>
    apply TermVarInEnvironment.typeVarExt
    apply xAinG.append_inl
    intro A' xA'inGG'
    exact xninGG A' xA'inGG'.typeVarExt

theorem TermVarInEnvironment.append_inr : [[x : A ∈ GG]] → [[x : A ∈ G, GG]]
  | .head => .head
  | .termVarExt xAinGG' xnex' => xAinGG'.append_inr |>.termVarExt xnex'
  | .typeVarExt xAinGG' => xAinGG'.append_inr |>.typeVarExt

theorem TermVarInEnvironment.TermVar_swap (x'inGxyGG : [[x' : A' ∈ G, x : A, y : B, GG]])
  (xney : x ≠ y) : [[x' : A' ∈ G, y : B, x : A, GG]] := by
  match x'inGxyGG.append_elim with
  | .inl ⟨x'inGxy, x'ninGG⟩ =>
    apply TermVarInEnvironment.append_inl _ x'ninGG
    match x'inGxy with
    | .head => exact .termVarExt .head xney.symm
    | .termVarExt x'inGx x'ney => match x'inGx with
      | .head => exact .head
      | .termVarExt x'inG x'nex => exact x'inG.termVarExt x'ney |>.termVarExt x'nex
  | .inr x'inGG => exact x'inGG.append_inr

theorem TermVarInEnvironment.subst (xAinG : [[x : A ∈ G]]) (aninG : [[a ∉ G]])
  : [[x : A [B / a] ∈ G [B / a] ]] := by
  rw [Environment.subst]
  induction G
  · case empty => cases xAinG
  · case termVarExt G' x' A' ih =>
    rw [Environment.subst.go]
    simp
    split
    · case isTrue sndeqtrue =>
      apply False.elim
      apply ne_false_of_eq_true sndeqtrue
      apply G'.subst_go_snd_eq_false_of_TermVarNotInEnvironment
      exact aninG.TermVar_drop
    · case isFalse sndeqfalse =>
      cases xAinG
      · case head => exact .head
      · case termVarExt xAinG' xnex' =>
        apply TermVarInEnvironment.termVarExt _ xnex'
        apply ih xAinG'
        exact aninG.TermVar_drop
  · case typeVarExt G' a' ih =>
    rw [Environment.subst.go]
    simp
    cases xAinG
    case typeVarExt xAinG' =>
    apply TermVarInEnvironment.typeVarExt
    apply ih xAinG'
    exact aninG.TypeVar_drop

theorem TermVarInEnvironment.unsubst (xAsinGs : [[x : A' ∈ G [B / a] ]]) (aninG : [[a ∉ G]])
  : ∃ A, [[x : A ∈ G]] ∧ A' = [[(A [B / a])]] := by
  rw [Environment.subst] at xAsinGs
  induction G
  · case empty => cases xAsinGs
  · case termVarExt G' x' A' ih =>
    rw [Environment.subst.go] at xAsinGs
    simp at xAsinGs
    split at xAsinGs
    · case isTrue sndeqtrue =>
      apply False.elim
      apply ne_false_of_eq_true sndeqtrue
      apply G'.subst_go_snd_eq_false_of_TermVarNotInEnvironment
      exact aninG.TermVar_drop
    · case isFalse sndeqfalse =>
      simp at xAsinGs
      cases xAsinGs
      · case head => exact Exists.intro A' ⟨.head, rfl⟩
      · case termVarExt xAinG' xnex' =>
        let ⟨A'', ⟨xA''inG', eq⟩⟩ := ih xAinG' aninG.TermVar_drop
        exact Exists.intro A'' ⟨xA''inG'.termVarExt xnex', eq⟩
  · case typeVarExt G' a' ih =>
    rw [Environment.subst.go] at xAsinGs
    simp at xAsinGs
    cases xAsinGs
    case typeVarExt xAinG' =>
    let ⟨A', ⟨xA'inG', eq⟩⟩ := ih xAinG' aninG.TypeVar_drop
    exact Exists.intro A' ⟨xA'inG'.typeVarExt, eq⟩

theorem TermVarNotInEnvironment.ε : [[x ∉ ε]] := fun _ xinε => by cases xinε

theorem TermVarNotInEnvironment.termVarExt (xninG : [[x ∉ G]]) (ynex : y ≠ x)
  : [[x ∉ G, y : A]] := by
  intro A' xA'inGy
  apply xninG A'
  cases xA'inGy
  · case head => contradiction
  · case termVarExt xA'inG _ => exact xA'inG

theorem TermVarNotInEnvironment.typeVarExt (xninG : [[x ∉ G]]) : [[x ∉ G, a]] := by
  intro A' xA'inGa
  apply xninG A'
  cases xA'inGa
  case typeVarExt xA'inG => exact xA'inG

judgement_syntax G " ⊢ " A : TypeWellFormedness

judgement TypeWellFormedness :=

a ∈ G
───── var
G ⊢ a

G ⊢ A
G ⊢ B
───────── arr
G ⊢ A → B

G, a ⊢ A
────────── forall'
G ⊢ ∀ a. A

theorem TypeWellFormedness.TypeVar_swap (Awf : [[G, b, a, GG ⊢ A]]) : [[G, a, b, GG ⊢ A]] := by
  cases Awf
  · case var a' a'inGbaGG =>
    match a'inGbaGG.append_elim with
    | .inl a'inGba =>
      cases a'inGba
      · case head =>
        by_cases a = b
        · case pos aeqb =>
          rw [aeqb]
          exact .var TypeVarInEnvironment.head.append_inl
        · case neg aneb =>
          exact .var <| .append_inl <| .typeVarExt .head aneb
      · case typeVarExt a'inGb a'nea =>
        cases a'inGb
        · case head => exact .var <| .append_inl .head
        · case typeVarExt a'inG a'neb =>
          exact .var <| .append_inl <| .typeVarExt (.typeVarExt a'inG a'nea) a'neb
    | .inr a'inGG => exact .var a'inGG.append_inr
  · case arr A' B A'wf Bwf =>
    exact .arr A'wf.TypeVar_swap Bwf.TypeVar_swap
  · case forall' a' A' A'wf =>
    apply TypeWellFormedness.forall'
    rw [← Environment.append]
    exact TypeWellFormedness.TypeVar_swap A'wf

theorem TypeWellFormedness.TypeVar_shadowed : [[G, a, a ⊢ A]] → [[G, a ⊢ A]]
  | .var a'inGaa => match a'inGaa with
    | .head => .var .head
    | .typeVarExt a'inGa _ => .var a'inGa
  | .arr A'wf Bwf => .arr A'wf.TypeVar_shadowed Bwf.TypeVar_shadowed
  | .forall' A'wf => .forall' <| A'wf.TypeVar_swap (GG := .empty)
      |>.TypeVar_swap (GG := .typeVarExt .empty a)
      |>.TypeVar_shadowed
      |>.TypeVar_swap (GG := .empty)

theorem TypeWellFormedness.TermVar_drop : [[G, x : A, GG ⊢ B]] → [[G, GG ⊢ B]]
  | .var ainGxGG => match ainGxGG.append_elim with
    | .inl (.termVarExt ainG) => .var ainG.append_inl
    | .inr ainGG => .var ainGG.append_inr
  | .arr A'wf B'wf => .arr A'wf.TermVar_drop B'wf.TermVar_drop
  | .forall' A'wf => .forall' <| A'wf.TermVar_drop (GG := .typeVarExt GG _)

theorem TypeWellFormedness.TermVar_intro : [[G, GG ⊢ B]] → [[G, x : A, GG ⊢ B]]
  | .var ainGappGG => match ainGappGG.append_elim with
    | .inl ainG => .var ainG.termVarExt.append_inl
    | .inr ainGG => .var ainGG.append_inr
  | .arr A'wf B'wf => .arr A'wf.TermVar_intro B'wf.TermVar_intro
  | .forall' A'wf => .forall' <| A'wf.TermVar_intro (GG := .typeVarExt GG _)

theorem TypeWellFormedness.TermVar_swap (Bwf : [[G, y : A', x : A, GG ⊢ B]])
  : [[G, x : A, y : A', GG ⊢ B]] := Bwf.TermVar_drop.TermVar_drop.TermVar_intro.TermVar_intro

theorem TypeWellFormedness.append_inr : [[G ⊢ A]] → [[GG, G ⊢ A]]
  | .var ainG => .var ainG.append_inr
  | .arr A'wf Bwf => .arr A'wf.append_inr Bwf.append_inr
  | .forall' A'wf => .forall' A'wf.append_inr

theorem TypeWellFormedness.TypeVar_shadowed_subst
  : [[ε, a, G, a, GG ⊢ A]] → [[(G, a) [B / a], GG ⊢ A]]
  | .var a'inεaGaGG =>
    match a'inεaGaGG.append_elim with
    | .inl a'inεa =>
      match a'inεa with
      | .head => .var TypeVarInEnvironment.head.subst.append_inl
      | .typeVarExt a'inε _ => by cases a'inε
    | .inr a'inGaGG => match a'inGaGG.append_elim with
      | .inl a'inGa => .var a'inGa.subst.append_inl
      | .inr a'inGG => .var a'inGG.append_inr
  | .arr A'wf B'wf => .arr A'wf.TypeVar_shadowed_subst B'wf.TypeVar_shadowed_subst
  | .forall' A'wf => .forall' <| A'wf.TypeVar_shadowed_subst (GG := GG.typeVarExt _)

theorem TypeWellFormedness.subst (Awf : [[ε, a, G ⊢ A]]) (Bwf : [[ε ⊢ B]])
  : [[G [B / a] ⊢ A [B / a] ]] := by
  cases Awf
  · case var a' a'inεaG =>
    rw [Type'.TypeVar_subst]
    split
    · case isTrue a'eqa =>
      exact Bwf.append_inr
    · case isFalse a'nea =>
      match a'inεaG.append_elim with
      | .inl a'inεa =>
        cases a'inεa
        · case head => contradiction
        · case typeVarExt => contradiction
      | .inr a'inG =>
        exact .var a'inG.subst
  · case arr A' B' A'wf B'wf => exact .arr (A'wf.subst Bwf) (B'wf.subst Bwf)
  · case forall' a' A' A'wf =>
    rw [Type'.TypeVar_subst]
    split
    · case isTrue a'eqa =>
      rw [a'eqa]
      rw [a'eqa] at A'wf
      exact .forall' <| A'wf.TypeVar_shadowed_subst (GG := .empty)
    · case isFalse a'nea => exact TypeWellFormedness.forall' <| A'wf.subst (G := G.typeVarExt a') Bwf

theorem Type'.subst_id_of_TypeWellFormedness_of_TypeVarNotInEnvironment (Awf : [[G ⊢ A]])
  (aninG : [[a ∉ G]]) : [[(A [B / a])]] = A := by
  match Awf with
  | .var a'inG =>
    rw [Type'.TypeVar_subst]
    split
    · case isTrue aeqa' =>
      rw [aeqa'.symm] at a'inG
      exact False.elim <| aninG a'inG
    · case isFalse => rfl
  | .arr A'wf B'wf =>
    rw [Type'.TypeVar_subst, Type'.subst_id_of_TypeWellFormedness_of_TypeVarNotInEnvironment A'wf aninG,
        Type'.subst_id_of_TypeWellFormedness_of_TypeVarNotInEnvironment B'wf aninG]
  | .forall' A'wf =>
    rw [Type'.TypeVar_subst]
    split
    · case isTrue => rfl
    · case isFalse anea' =>
      rw [Type'.subst_id_of_TypeWellFormedness_of_TypeVarNotInEnvironment A'wf]
      have anea' : a ≠ _ := anea'
      exact aninG.typeVarExt anea'.symm

judgement_syntax a " ∈ " "ftv" "(" A ")" : InFreeTypeVars

judgement InFreeTypeVars :=

────────── var
a ∈ ftv(a)

a ∈ ftv(A)
────────────── arrl
a ∈ ftv(A → B)

a ∈ ftv(B)
────────────── arrr
a ∈ ftv(A → B)

a ∈ ftv(A)
a ≠ b
─────────────── forall'
a ∈ ftv(∀ b. A)

judgement_syntax a " ∉ " "ftv" "(" A ")" : NotInFreeTypeVars

def NotInFreeTypeVars a A := ¬[[a ∈ ftv(A)]]

theorem NotInFreeTypeVars.of_TypeWellFormedness_of_TypeVarNotInEnvironment (Awf : [[G ⊢ A]])
  (aninG : [[a ∉ G]]) : [[a ∉ ftv(A)]] := by
  intro ain
  match A, Awf with
  | .var a', .var a'inG =>
    let .var := ain
    exact aninG a'inG
  | .arr A' B, .arr A'wf Bwf => match ain with
    | .arrl ainA' =>
      exact NotInFreeTypeVars.of_TypeWellFormedness_of_TypeVarNotInEnvironment A'wf aninG <| ainA'
    | .arrr ainB =>
      exact NotInFreeTypeVars.of_TypeWellFormedness_of_TypeVarNotInEnvironment Bwf aninG <| ainB
  | .forall' a' A', .forall' A'wf =>
    let .forall' ainftvA' anea' := ain
    apply NotInFreeTypeVars.of_TypeWellFormedness_of_TypeVarNotInEnvironment A'wf _ ainftvA'
    exact aninG.typeVarExt anea'.symm

theorem InFreeTypeVars.unsubst (ain : [[a ∈ ftv(A [B / b])]]) (Bwf : [[ε ⊢ B]]) : [[a ∈ ftv(A)]] := by
  match A with
  | .var a' =>
    rw [Type'.TypeVar_subst] at ain
    split at ain
    · case isTrue a'eqa =>
      exact False.elim <|
        NotInFreeTypeVars.of_TypeWellFormedness_of_TypeVarNotInEnvironment Bwf
          TypeVarNotInEnvironment.ε ain
    · case isFalse a'neb =>
      let .var := ain
      exact .var
  | .arr A' B' =>
    rw [Type'.TypeVar_subst] at ain
    match ain with
    | .arrl ain => exact .arrl <| ain.unsubst Bwf
    | .arrr ain => exact .arrr <| ain.unsubst Bwf
  | .forall' a' A' =>
    rw [Type'.TypeVar_subst] at ain
    split at ain
    · case isTrue a'eqb => exact ain
    · case isFalse a'neb =>
      let .forall' ain anea' := ain
      exact .forall' (ain.unsubst Bwf) anea'

theorem NotInFreeTypeVars.subst_id (aninftvA : [[a ∉ ftv(A)]]) : [[(A [B / a])]] = A := by
  match A with
  | .var a' =>
    rw [Type'.TypeVar_subst, if_neg]
    intro a'eqa
    rw [a'eqa] at aninftvA
    exact aninftvA .var
  | .arr A' B' =>
    rw [Type'.TypeVar_subst, NotInFreeTypeVars.subst_id, NotInFreeTypeVars.subst_id]
    · intro ainftvB'
      exact aninftvA <| .arrr ainftvB'
    · intro ainftvA'
      exact aninftvA <| .arrl ainftvA'
  | .forall' a' A' =>
    rw [Type'.TypeVar_subst]
    split
    · case isTrue => rfl
    · case isFalse a'nea =>
      have a'nea : a ≠ a' := a'nea
      rw [NotInFreeTypeVars.subst_id]
      intro ainftvA'
      exact aninftvA <| InFreeTypeVars.forall' ainftvA' a'nea

judgement_syntax x " ∈ " "fv" "(" E ")" : InFreeTermVars

judgement InFreeTermVars :=

───────── var
x ∈ fv(x)

x ∈ fv(E)
x ≠ y
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

judgement_syntax x " ∉ " "fv" "(" E ")" : NotInFreeTermVars

def NotInFreeTermVars x E := ¬[[x ∈ fv(E)]]

judgement_syntax G " ⊢ " a " ∈ " "fvftv" "(" E ")" : InFreeTermVars'Types'FreeTypeVars

judgement InFreeTermVars'Types'FreeTypeVars :=

x ∈ fv(E)
x : A ∈ G
a ∈ ftv(A)
──────────────── mk
G ⊢ a ∈ fvftv(E)

judgement_syntax G " ⊢ " a " ∉ " "fvftv" "(" E ")" : NotInFreeTermVars'Types'FreeTypeVars

def NotInFreeTermVars'Types'FreeTypeVars G a E := ¬[[G ⊢ a ∈ fvftv(E)]]

theorem NotInFreeTermVars'Types'FreeTypeVars.TermVar_swap
  (anin : [[G, y : A', x : A, GG ⊢ a ∉ fvftv(E)]]) (xney : x ≠ y)
  : [[G, x : A, y : A', GG ⊢ a ∉ fvftv(E)]] := by
  intro ain
  apply anin
  let .mk x'infv x'A'in ainftvA' := ain
  exact InFreeTermVars'Types'FreeTypeVars.mk x'infv (x'A'in.TermVar_swap xney) ainftvA'

theorem NotInFreeTermVars'Types'FreeTypeVars.TermVar_shadowed (anin : [[G, x : A_shadowed, GG, x : A, GGG ⊢ a ∉ fvftv(E)]])
  : [[G, GG, x : A, GGG ⊢ a ∉ fvftv(E)]] := by
  intro ain
  apply anin
  cases ain
  case mk x' A' x'A'in ainftvA' x'infv =>
  apply InFreeTermVars'Types'FreeTypeVars.mk x'infv _ ainftvA'
  match x'A'in.append_elim with
  | .inl ⟨x'A'inG, x'ninGGxGGG⟩ =>
    apply TermVarInEnvironment.append_inl _ x'ninGGxGGG
    by_cases x' = x
    · case pos x'eqx =>
      apply False.elim
      rw [x'eqx] at x'ninGGxGGG
      apply x'ninGGxGGG A
      apply TermVarInEnvironment.head.append_inl
      intro A'' xA''inGG
      apply x'ninGGxGGG A''
      exact xA''inGG.append_inr
    · case neg x'nex => exact x'A'inG.termVarExt x'nex
  | .inr x'A'inGGxGGG => exact x'A'inGGxGGG.append_inr

theorem NotInFreeTermVars'Types'FreeTypeVars.append_elr (anin : [[G, GG ⊢ a ∉ fvftv(E)]])
  : [[GG ⊢ a ∉ fvftv(E)]] := by
  intro ain
  apply anin
  let .mk x'infv x'A'inG ainftv := ain
  exact InFreeTermVars'Types'FreeTypeVars.mk x'infv x'A'inG.append_inr ainftv

theorem NotInFreeTermVars'Types'FreeTypeVars.Environment_subst (anin : [[G ⊢ a ∉ fvftv(E)]])
  (Awf : [[ε ⊢ A]]) (bninG : [[b ∉ G]]) : [[G [A / b] ⊢ a ∉ fvftv(E)]] := by
  intro ain
  apply anin
  let .mk x'infv x'A'inG ainftv := ain
  let ⟨_, ⟨xA'inG', eq⟩⟩ := x'A'inG.unsubst bninG
  rw [eq] at ainftv
  exact .mk x'infv xA'inG' <| ainftv.unsubst Awf

theorem NotInFreeTermVars'Types'FreeTypeVars.appl (anin : [[G ⊢ a ∉ fvftv(E F)]])
  : [[G ⊢ a ∉ fvftv(E)]] := by
  intro ain
  apply anin
  let .mk x'infv x'A'inG ainftv := ain
  exact .mk x'infv.appl x'A'inG ainftv

theorem NotInFreeTermVars'Types'FreeTypeVars.appr (anin : [[G ⊢ a ∉ fvftv(E F)]])
  : [[G ⊢ a ∉ fvftv(F)]] := by
  intro ain
  apply anin
  let .mk x'infv x'A'inG ainftv := ain
  exact .mk x'infv.appr x'A'inG ainftv

theorem NotInFreeTermVars'Types'FreeTypeVars.typeGen (anin : [[G ⊢ a ∉ fvftv(Λ b. E)]])
  : [[G ⊢ a ∉ fvftv(E)]] := by
  intro ain
  apply anin
  let .mk x'infv x'A'inG ainftv := ain
  exact .mk x'infv.typeGen x'A'inG ainftv

theorem NotInFreeTermVars'Types'FreeTypeVars.typeApp (anin : [[G ⊢ a ∉ fvftv(E [A])]])
  : [[G ⊢ a ∉ fvftv(E)]] := by
  intro ain
  apply anin
  let .mk x'infv x'A'inG ainftv := ain
  exact .mk x'infv.typeApp x'A'inG ainftv

judgement_syntax G " ⊢ " E " : " A : Typing

judgement Typing :=

x : A ∈ G
───────── var
G ⊢ x : A

G ⊢ A
G, x : A ⊢ E : B
────────────────────── lam
G ⊢ λ x : A. E : A → B

G ⊢ E : A → B
G ⊢ F : A
───────────── app
G ⊢ E F : B

G ⊢ a ∉ fvftv(E)
G, a ⊢ E : A
─────────────────── typeGen
G ⊢ Λ a. E : ∀ a. A

G ⊢ E : ∀ a. A
G ⊢ B
───────────────────── typeApp
G ⊢ E [B] : A [B / a]

theorem Typing.TermVar_swap (EtyB : [[G, y : A', x : A, GG ⊢ E : B]]) (xney : x ≠ y)
  : [[G, x : A, y : A', GG ⊢ E : B]] :=
  match EtyB with
  | .var x'BinGyxappGG =>
    match x'BinGyxappGG.append_elim with
    | .inl ⟨x'BinGyx, x'ninGG⟩ => match x'BinGyx with
      | .head => .var <| TermVarInEnvironment.append_inl (.termVarExt .head xney) x'ninGG
      | .termVarExt x'BinGy x'nex => match x'BinGy with
        | .head => .var <| .append_inl .head x'ninGG
        | .termVarExt x'BinG x'ney =>
          .var <| x'BinG.termVarExt x'nex |>.termVarExt x'ney |>.append_inl x'ninGG
    | .inr x'BinGG => .var x'BinGG.append_inr
  | .lam A'wf E'tyB' =>
    .lam A'wf.TermVar_swap <| E'tyB'.TermVar_swap (GG := GG.termVarExt ..) xney
  | .app E'tyA'arrB F'tyA' => .app (E'tyA'arrB.TermVar_swap xney) (F'tyA'.TermVar_swap xney)
  | .typeGen a'nin E'tyA' =>
    .typeGen (a'nin.TermVar_swap xney) <| E'tyA'.TermVar_swap (GG := GG.typeVarExt _) xney
  | .typeApp E'ty B'wf => .typeApp (E'ty.TermVar_swap xney) B'wf.TermVar_swap

theorem Typing.False_of_in_fv_of_nin_Environment (EtyA : [[G ⊢ E : A]]) (xinfvE : [[x ∈ fv(E)]])
  (xninG : [[x ∉ G]]) : False :=
  match EtyA, xinfvE with
  | .var x'AinG, .var => xninG _ x'AinG
  | .lam _ E'tyB', .lam xinfvE' xnex' =>
    E'tyB'.False_of_in_fv_of_nin_Environment xinfvE' (xninG.termVarExt xnex'.symm)
  | .app E'tyA'arrA F'tyA', .appl xinfvE' =>
    E'tyA'arrA.False_of_in_fv_of_nin_Environment xinfvE' xninG
  | .app _ F'tyA', .appr xinfvF' => F'tyA'.False_of_in_fv_of_nin_Environment xinfvF' xninG
  | .typeGen _ E'tyA', .typeGen xinfvE' =>
    E'tyA'.False_of_in_fv_of_nin_Environment xinfvE' xninG.typeVarExt
  | .typeApp E'ty B'wf, .typeApp xinfvE' => E'ty.False_of_in_fv_of_nin_Environment xinfvE' xninG

theorem NotInFreeTermVars'Types'FreeTypeVars.append_inr (anin : [[G ⊢ a ∉ fvftv(E)]])
  (EtyA : [[G, b ⊢ E : A]]) : [[GG, G ⊢ a ∉ fvftv(E)]] := fun ain =>
  anin <|
    let .mk x'infv x'A'inGGappG ainftv := ain
    match x'A'inGGappG.append_elim with
    | .inl ⟨_, x'ninG⟩ =>
      False.elim <| EtyA.False_of_in_fv_of_nin_Environment x'infv x'ninG.typeVarExt
    | .inr x'A'inG => .mk x'infv x'A'inG ainftv

theorem Typing.append_inr : [[G ⊢ E : A]] → [[GG, G ⊢ E : A]]
  | .var xAinG => .var xAinG.append_inr
  | .lam A'wf E'tyB => .lam A'wf.append_inr E'tyB.append_inr
  | .app FtyA' E'tyA'arrA => .app FtyA'.append_inr E'tyA'arrA.append_inr
  | .typeGen a'nin E'tyA' => .typeGen (a'nin.append_inr E'tyA') E'tyA'.append_inr
  | .typeApp E'ty Bwf => .typeApp E'ty.append_inr Bwf.append_inr

theorem Typing.TermVar_shadowed : [[G, x : A_shadowed, GG, x : A, GGG ⊢ E : B]] → [[G, GG, x : A, GGG ⊢ E : B]]
  | var x'BinGxGGxGGG =>
    match x'BinGxGGxGGG.append_elim with
    | .inl ⟨x'BinGx, x'ninGGxGGG⟩ =>
      match x'BinGx with
      | .head => False.elim <| x'ninGGxGGG A <| TermVarInEnvironment.append_inl .head
          fun A' xA'inGGG => x'ninGGxGGG A' xA'inGGG.append_inr
      | .termVarExt x'BinG _ => .var <| x'BinG.append_inl x'ninGGxGGG
    | .inr x'BinGGxGGG => .var x'BinGGxGGG.append_inr
  | lam A'wf E'tyB' => .lam A'wf.TermVar_drop <| E'tyB'.TermVar_shadowed (GGG := GGG.termVarExt ..)
  | app E'tyA'arrB FtyA' => .app E'tyA'arrB.TermVar_shadowed FtyA'.TermVar_shadowed
  | typeGen a'nin E'tyA' => .typeGen a'nin.TermVar_shadowed <| E'tyA'.TermVar_shadowed (GGG := GGG.typeVarExt _)
  | typeApp E'ty B'wf => .typeApp E'ty.TermVar_shadowed B'wf.TermVar_drop

theorem Typing.TypeVar_shadowed_subst (EtyA : [[ε, a, G, a, GG ⊢ E : A]]) (Bwf : [[ε ⊢ B]])
  (aninG : [[a ∉ G]])
  (ih : ∀ x : TermVar, [[x ∈ fv(E)]] → (∃ A, [[x : A ∈ GG]]) ∨ ∀ A, [[x : A ∈ G]] → [[a ∉ ftv(A)]])
  : [[(G, a) [B / a], GG ⊢ E : A]] := by
  cases EtyA
  · case var x xAinεaGaGG =>
    match xAinεaGaGG.append_elim with
    | .inl ⟨xAinεa, _⟩ =>
      cases xAinεa
      case typeVarExt xAinε =>
      cases xAinε
    | .inr xAinGaGG => match xAinGaGG.append_elim with
      | .inl ⟨xAinGa, xninGG⟩ =>
        apply Typing.var
        apply TermVarInEnvironment.append_inl _ xninGG
        rw [← Environment.subst_typeVarExt_eq_typeVarExt_subst]
        apply TermVarInEnvironment.typeVarExt
        cases xAinGa
        case a.typeVarExt xAinG =>
        have aninftvA : [[a ∉ ftv(A)]] := by
          match ih x .var with
          | .inl ⟨A', xA'inGG⟩ => exact False.elim <| xninGG A' xA'inGG
          | .inr h => exact h A xAinG
        rw [← NotInFreeTypeVars.subst_id aninftvA]
        exact xAinG.subst aninG
      | .inr xAinGG => exact .var xAinGG.append_inr
  · case lam A' x E' B' A'wf E'tyB' =>
    apply Typing.lam A'wf.TypeVar_shadowed_subst
    apply E'tyB'.TypeVar_shadowed_subst (GG := GG.termVarExt x A') Bwf aninG
    intro x' x'infvE'
    by_cases x' = x
    · case pos x'eqx =>
      rw [x'eqx]
      exact .inl <| Exists.intro A' .head
    · case neg x'nex =>
      match ih x' (x'infvE'.lam x'nex) with
      | .inl ⟨A'', x'A''inGG⟩ => exact .inl <| Exists.intro A'' <| x'A''inGG.termVarExt x'nex
      | .inr h => exact .inr h
  · case app E' A' F FtyA' E'tyA'arrA =>
    exact .app (E'tyA'arrA.TypeVar_shadowed_subst Bwf aninG (ih · ·.appl))
      (FtyA'.TypeVar_shadowed_subst Bwf aninG (ih · ·.appr))
  · case typeGen a' E' A' a'nin E'tyA' =>
    apply Typing.typeGen _ <| E'tyA'.TypeVar_shadowed_subst (GG := GG.typeVarExt a') Bwf aninG _
    · intro a'in
      apply a'nin
      let .mk x'infv x'A'in a'inftv := a'in
      match x'A'in.append_elim with
      | .inl ⟨.typeVarExt x'A'in, x'ninGG⟩ =>
        let ⟨A'', ⟨x'A''in, eq⟩⟩ := x'A'in.unsubst aninG
        rw [eq] at a'inftv
        exact .mk x'infv (x'A''in.typeVarExt.append_inl x'ninGG).append_inr <| a'inftv.unsubst Bwf
      | .inr x'A'inGG => exact .mk x'infv x'A'inGG.append_inr.append_inr a'inftv
    · intro x xinfvE'
      match ih x xinfvE'.typeGen with
      | .inl ⟨A'', x'A''inGG⟩ => exact .inl <| Exists.intro A'' <| x'A''inGG.typeVarExt
      | .inr h => exact .inr h
  · case typeApp E' a' A' B' E'ty B'wf =>
    exact .typeApp (E'ty.TypeVar_shadowed_subst Bwf aninG (ih · ·.typeApp)) B'wf.TypeVar_shadowed_subst

theorem NotInFreeTermVars.of_Typing_of_TermVarNotInEnvironment (EtyA : [[G ⊢ E : A]])
  (xninG : [[x ∉ G]]) : [[x ∉ fv(E)]] := by
  intro ain
  match EtyA, ain with
  | .var x'inG, .var => exact xninG A x'inG
  | .lam _ E'tyB, .lam xinE' xnex' =>
    apply NotInFreeTermVars.of_Typing_of_TermVarNotInEnvironment E'tyB _ xinE'
    exact xninG.termVarExt xnex'.symm
  | .app E'tyA'arrA _, .appl xinE' =>
    exact NotInFreeTermVars.of_Typing_of_TermVarNotInEnvironment E'tyA'arrA xninG xinE'
  | .app _ F'tyA', .appr xinF' =>
    exact NotInFreeTermVars.of_Typing_of_TermVarNotInEnvironment F'tyA' xninG xinF'
  | .typeGen _ E'tyA', .typeGen xinE' =>
    exact NotInFreeTermVars.of_Typing_of_TermVarNotInEnvironment E'tyA' xninG.typeVarExt xinE'
  | .typeApp E'ty _, .typeApp xinE' =>
    exact NotInFreeTermVars.of_Typing_of_TermVarNotInEnvironment E'ty xninG xinE'

theorem InFreeTermVars.unTermVar_subst (xin : [[x ∈ fv(E [F / y])]]) (FtyA : [[ε ⊢ F : A]])
  : [[x ∈ fv(E)]] := by
  match E with
  | .var x' =>
    rw [Term.TermVar_subst] at xin
    split at xin
    · case isTrue x'eqx =>
      exact False.elim <|
        NotInFreeTermVars.of_Typing_of_TermVarNotInEnvironment FtyA TermVarNotInEnvironment.ε xin
    · case isFalse x'nex =>
      let .var := xin
      exact .var
  | .lam x' A' E' =>
    rw [Term.TermVar_subst] at xin
    split at xin
    · case isTrue x'eqy => exact xin
    · case isFalse x'ney =>
      let .lam xinE' xnex' := xin
      exact .lam (xinE'.unTermVar_subst FtyA) xnex'
  | .app E' F' =>
    rw [Term.TermVar_subst] at xin
    match xin with
    | .appl xinE' => exact .appl <| xinE'.unTermVar_subst FtyA
    | .appr xinF' => exact .appr <| xinF'.unTermVar_subst FtyA
  | .typeGen a' E' =>
    rw [Term.TermVar_subst] at xin
    let .typeGen xinE' := xin
    exact .typeGen <| xinE'.unTermVar_subst FtyA
  | .typeApp E' A'' =>
    rw [Term.TermVar_subst] at xin
    let .typeApp xinE' := xin
    exact .typeApp <| xinE'.unTermVar_subst FtyA

theorem NotInFreeTermVars'Types'FreeTypeVars.Term_TermVar_subst (anin : [[G ⊢ a ∉ fvftv(E)]])
  (FtyA : [[ε ⊢ F : A]]) : [[G ⊢ a ∉ fvftv(E [F / x])]] := by
  intro ain
  apply anin
  cases ain
  case mk x' A' x'A'inG ainftv x'infv =>
  exact InFreeTermVars'Types'FreeTypeVars.mk (x'infv.unTermVar_subst FtyA) x'A'inG ainftv

theorem InFreeTermVars.unTypeVar_subst (xin : [[x ∈ fv(E [B / b])]]) : [[x ∈ fv(E)]] := by
  match E with
  | .var x' =>
    rw [Term.TypeVar_subst] at xin
    exact xin
  | .lam x' A' E' =>
    rw [Term.TypeVar_subst] at xin
    let .lam xinE' xnex' := xin
    exact InFreeTermVars.lam xinE'.unTypeVar_subst xnex'
  | .app E' F' =>
    rw [Term.TypeVar_subst] at xin
    match xin with
    | .appl xinE' => exact .appl xinE'.unTypeVar_subst
    | .appr xinF' => exact .appr xinF'.unTypeVar_subst
  | .typeGen a' E' =>
    rw [Term.TypeVar_subst] at xin
    split at xin
    · case isTrue a'eqb => exact xin
    · case isFalse a'neb =>
      let .typeGen xinE' := xin
      exact .typeGen xinE'.unTypeVar_subst
  | .typeApp E' A'' =>
    rw [Term.TypeVar_subst] at xin
    let .typeApp xinE' := xin
    exact .typeApp xinE'.unTypeVar_subst

theorem NotInFreeTermVars'Types'FreeTypeVars.Term_TypeVar_subst (anin : [[G ⊢ a ∉ fvftv(E)]])
  : [[G ⊢ a ∉ fvftv(E [A / b])]] := by
  intro ain
  apply anin
  cases ain
  case mk x' A' x'A'inG ainftv x'infv =>
  exact InFreeTermVars'Types'FreeTypeVars.mk x'infv.unTypeVar_subst x'A'inG ainftv

theorem Typing.TermVar_subst_preservation (EtyB : [[ε, x : A, G ⊢ E : B]]) (xninG : [[x ∉ G]])
  (FtyA : [[ε ⊢ F : A]]) : [[G ⊢ E [F / x] : B]] := by
  match EtyB with
  | .var x'BinεxappG =>
    rw [Term.TermVar_subst]
    split
    · case isTrue xeqx' =>
      rw [← xeqx'] at x'BinεxappG
      match x'BinεxappG.append_elim with
      | .inl ⟨xBinεx, _⟩ =>
        cases xBinεx
        · case head => exact FtyA.append_inr
        · case termVarExt xBinε xnex => contradiction
      | .inr xBinG =>
        exact False.elim <| xninG B xBinG
    · case isFalse x'nex =>
      match x'BinεxappG.append_elim with
      | .inl ⟨xBinGx, xninG⟩ =>
        cases xBinGx
        · case head => contradiction
        · case termVarExt x'Binε _ => cases x'Binε
      | .inr x'BinG => exact .var x'BinG
  | .lam A'wf E'tyB' =>
    rw [Term.TermVar_subst]
    split
    · case isTrue xeqx' =>
      rw [← xeqx', G.empty_append]
      rw [← xeqx'] at E'tyB'
      exact .lam A'wf.TermVar_drop <| E'tyB'.TermVar_shadowed (GGG := .empty)
    · case isFalse xnex' =>
      rw [G.empty_append]
      apply Typing.lam A'wf.TermVar_drop
      rw [← G.empty_append]
      apply E'tyB'.TermVar_subst_preservation (G := G.termVarExt ..) _ FtyA
      have xnex' : x ≠ _ := xnex'
      exact xninG.termVarExt xnex'.symm
  | .app E'tyA'arrB F'tyA' =>
    exact .app (E'tyA'arrB.TermVar_subst_preservation xninG FtyA) (F'tyA'.TermVar_subst_preservation xninG FtyA)
  | .typeGen a'nin E'tyA' =>
    apply Typing.typeGen <| a'nin.append_elr.Term_TermVar_subst FtyA
    apply E'tyA'.TermVar_subst_preservation (G := G.typeVarExt _) _ FtyA
    exact xninG.typeVarExt
  | .typeApp E'ty B'wf =>
    apply Typing.typeApp <| E'ty.TermVar_subst_preservation xninG FtyA
    rw [G.empty_append]
    exact B'wf.TermVar_drop

theorem Typing.TypeVar_subst_preservation (EtyA : [[ε, a, G ⊢ E : A]]) (aninG : [[a ∉ G]])
  (Bwf : [[ε ⊢ B]]) : [[G [B / a] ⊢ E [B / a] : A [B / a] ]] := by
  cases EtyA
  · case var x xAinεaappG => match xAinεaappG.append_elim with
    | .inr xAinG => exact .var <| xAinG.subst aninG
  · case lam A' x E' B' A'wf E'tyB' =>
    rw [Term.TypeVar_subst]
    rw [← Environment.append] at E'tyB'
    apply Typing.lam (A'wf.subst Bwf)
    rw [Environment.subst_termVarExt_eq_termVarExt_subst_of_TypeVarNotInEnvironment aninG]
    exact E'tyB'.TypeVar_subst_preservation (G := G.termVarExt x A') aninG.termVarExt Bwf
  · case app E' A' F FtyA' E'tyA'arrA =>
    exact .app (E'tyA'arrA.TypeVar_subst_preservation aninG Bwf) (FtyA'.TypeVar_subst_preservation aninG Bwf)
  · case typeGen a' E' A' a'nin E'tyA' =>
    rw [Term.TypeVar_subst]
    split
    · case isTrue aeqa' =>
      rw [← aeqa', ← Type'.subst_shadowed_forall]
      rw [← aeqa'] at E'tyA' a'nin
      apply Typing.typeGen <| a'nin.append_elr.Environment_subst Bwf aninG
      rw [Environment.subst_typeVarExt_eq_typeVarExt_subst]
      apply E'tyA'.TypeVar_shadowed_subst (GG := .empty) Bwf aninG
      intro x xinfvE'
      right
      intro A'' xA''inG ainftvA''
      exact a'nin <| InFreeTermVars'Types'FreeTypeVars.mk xinfvE' xA''inG.append_inr ainftvA''
    · case isFalse anea' =>
      rw [Type'.TypeVar_subst, if_neg anea']
      apply Typing.typeGen <| a'nin.append_elr.Term_TypeVar_subst.Environment_subst Bwf aninG
      rw [Environment.subst_typeVarExt_eq_typeVarExt_subst]
      have anea' : a ≠ a' := anea'
      exact E'tyA'.TypeVar_subst_preservation (G := G.typeVarExt a') (aninG.typeVarExt anea'.symm) Bwf
  · case typeApp E' a' A' B' E'ty B'wf =>
    rw [Term.TypeVar_subst]
    by_cases a' = a
    · case pos a'eqa =>
      rw [a'eqa, Type'.subst_subst]
      rw [a'eqa] at E'ty
      apply Typing.typeApp _ (B'wf.subst Bwf)
      rw [Type'.subst_shadowed_forall B]
      exact E'ty.TypeVar_subst_preservation aninG Bwf
    · case neg a'nea =>
      -- TODO: Probably need to use alpha equivalence to avoid issues when B' contains a.
      have : ((A'.TypeVar_subst a' B').TypeVar_subst a B) = (A'.TypeVar_subst a B).TypeVar_subst a' (B'.TypeVar_subst a B) := sorry
      rw [this]
      apply Typing.typeApp _ <| B'wf.subst Bwf
      rw [Type'.forall_subst_eq_subst_forall a'nea]
      exact E'ty.TypeVar_subst_preservation aninG Bwf

judgement_syntax E " -> " F : OperationalSemantics

judgement OperationalSemantics :=

E -> E'
─────────── appl
E F -> E' F

F -> F'
─────────── appr
V F -> V F'

─────────────────────────── lamApp
(λ x : A. E) V -> E [V / x]

E -> E'
─────────────── typeApp
E [A] -> E' [A]

───────────────────────── typeGenApp
(Λ a. E) [A] -> E [A / a]

theorem preservation (EtyA : [[ε ⊢ E : A]]) (EstepF : [[E -> F]]) : [[ε ⊢ F : A]] :=
  match EstepF, EtyA with
  | .appl E'stepE'next, .app E'tyA'arrA FtyA' => .app (preservation E'tyA'arrA E'stepE'next) FtyA'
  | .appr FstepFnext, .app VtyA'arrA FtyA' => .app VtyA'arrA <| preservation FtyA' FstepFnext
  | .lamApp, .app (.lam _ E'tyA) VtyA'' =>
      E'tyA.TermVar_subst_preservation (G := .empty) TermVarNotInEnvironment.ε VtyA''
  | .typeApp E'stepE'next, .typeApp E'ty A'wf => .typeApp (preservation E'ty E'stepE'next) A'wf
  | .typeGenApp, .typeApp (.typeGen _ E'tyA'') A'wf =>
    E'tyA''.TypeVar_subst_preservation (G := .empty) TypeVarNotInEnvironment.ε A'wf

theorem progress (EtyA : [[ε ⊢ E : A]]) : (∃ F, [[E -> F]]) ∨ ∃ V : Value, V.val = E :=
  match E, EtyA with
  | .lam x A' E', _ =>
    .inr <| Exists.intro { val := .lam x A' E', property := .lam } rfl
  | .app E' F', .app E'tyA'arrA F'tyA' =>
    match progress E'tyA'arrA with
    | .inl ⟨E'_next, E'stepE'_next⟩ => .inl <| Exists.intro (E'_next.app F') (.appl E'stepE'_next)
    | .inr ⟨VE', VE'eqE'⟩ => by
      match progress F'tyA' with
      | .inl ⟨F'_next, F'stepF'_next⟩ =>
        rw [← VE'eqE']
        exact .inl <| Exists.intro (VE'.val.app F'_next) (.appr F'stepF'_next)
      | .inr ⟨VF', VF'eqF'⟩ =>
        have E'val := VE'.property
        rw [VE'eqE'] at E'val
        match E' with
        | .lam x A' E'' =>
          rw [← VF'eqF']
          exact .inl <| Exists.intro (E''.TermVar_subst x VF'.val) .lamApp
  | .typeGen a E', _ =>
    .inr <| Exists.intro { val := .typeGen a E', property := .typeGen } rfl
  | .typeApp E' A', .typeApp E'ty A'wf =>
    match progress E'ty with
    | .inl ⟨E'_next, E'stepE'_next⟩ =>
      .inl <| Exists.intro (E'_next.typeApp A') <| .typeApp E'stepE'_next
    | .inr ⟨VE', VE'eqE'⟩ => by
      have E'val := VE'.property
      rw [VE'eqE'] at E'val
      match E' with
      | .typeGen a E'' => exact .inl <| Exists.intro (E''.TypeVar_subst a A') .typeGenApp

filter "LottExamples/SystemF/main.tex" "LottExamples/SystemF/main.mng"

end LottExamples.SystemF
