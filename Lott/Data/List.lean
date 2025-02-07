import Lott.Data.Nat

namespace List

/-
As suggested by Joachim Breitner on Zulip: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Internalizing.20congruence.20lemmas/near/398694086
-/
@[specialize]
def mapMem (as : List α) (f : (a : α) → a ∈ as → β) : List β := match as with
  | [] => []
  | a :: as' => f a (.head _) :: as'.mapMem (f · <| ·.tail _)

@[simp]
theorem mapMem_eq_map {as : List α} : as.mapMem (fun a _ => f a) = as.map f := by
  match as with
  | [] => rfl
  | a :: as' => rw [mapMem, map, as'.mapMem_eq_map]

theorem map_singleton_flatten (xs : List α) : (xs.map fun x => [f x]).flatten = xs.map f :=
  match xs with
  | [] => rfl
  | x :: xs' => by rw [List.map, List.map, List.flatten, List.singleton_append, xs'.map_singleton_flatten]

theorem not_mem_append' {xs ys : List α} : z ∉ xs ++ ys ↔ z ∉ xs ∧ z ∉ ys where
  mp zninxsys := ⟨(zninxsys <| mem_append.mpr <| .inl ·), (zninxsys <| mem_append.mpr <| .inr ·)⟩
  mpr | ⟨xninxs, xninys⟩, xinxsys => match mem_append.mp xinxsys with
    | .inl xinxs => xninxs xinxs
    | .inr xinys => xninys xinys

theorem not_mem_cons : x ∉ y :: xs ↔ x ≠ y ∧ x ∉ xs where
  mp nmem := ⟨ne_of_not_mem_cons nmem, not_mem_of_not_mem_cons nmem⟩
  mpr | ⟨ne, nmem⟩ => not_mem_cons_of_ne_of_not_mem ne nmem

theorem not_mem_flatten : x ∉ flatten xss ↔ ∀ xs ∈ xss, x ∉ xs where
  mp xnmem xs xsin := by
    let _ :: xss' := xss
    rw [flatten] at xnmem
    match xsin with
    | .head _ => exact List.not_mem_append'.mp xnmem |>.left
    | .tail _ xsin' =>
      apply not_mem_flatten.mp <| List.not_mem_append'.mp xnmem |>.right
      exact xsin'
  mpr nmem_of_mem := by
    match xss with
    | [] =>
      rw [List.flatten_nil]
      intro xin
      nomatch xin
    | xs :: xss' =>
      rw [List.flatten]
      exact List.not_mem_append'.mpr ⟨
        nmem_of_mem _ <| .head _,
        not_mem_flatten.mpr fun _ mem => nmem_of_mem _ <| .tail _ mem
      ⟩

theorem exists_gt (xs : List Nat)
  : ∃ n : Nat, ∀ m : Nat, m ∈ xs → m < n := match xs with
  | [] => .intro 0 fun x' x'in => nomatch x'in
  | x :: xs' =>
    let ⟨nxs', nxs'gt⟩ := xs'.exists_gt
    let n := max (x + 1) nxs'
    .intro n fun x' x'inxs => match List.mem_cons.mp x'inxs with
      | .inl h => by
        rw [h]
        dsimp only [n]
        rw [Nat.max_def]
        split
        · case isTrue h => exact Nat.lt_of_succ_le h
        · case isFalse h => exact Nat.lt_succ_self _
      | .inr x'inxs' => Nat.lt_of_lt_of_le (nxs'gt x' x'inxs') <| Nat.le_max_right _ _

theorem exists_fresh (xs : List Nat) : ∃ n, n ∉ xs :=
  let ⟨nxs, nxsgt⟩ := xs.exists_gt
  .intro nxs fun nxsinxs => Nat.not_le_of_lt (nxsgt _ nxsinxs) <| Nat.le_refl _

theorem le_sum_of_mem' {as : List Nat} (h : a ∈ as) : a ≤ as.sum := by
  match h with
  | .head _ =>
    rw [sum_cons]
    exact Nat.le_add_right _ _
  | .tail _ h' =>
    rw [sum_cons]
    exact Nat.le_trans (Nat.le_add_left ..) <| Nat.add_le_add_iff_left.mpr <| le_sum_of_mem' h'

theorem not_mem_singleton : a ∉ [b] ↔ a ≠ b :=
  ⟨(· <| mem_singleton.mpr ·), (· <| mem_singleton.mp ·)⟩

theorem eq_of_map_eq_map_of_inj {α β : Type} {f : α → β} {l₀ l₁ : List α}
  (eq : List.map f l₀ = List.map f l₁) (finj : ∀ x ∈ l₀, ∀ y ∈ l₁, f x = f y → x = y)
  : l₀ = l₁ := by
  match l₁ with
  | [] =>
    rw [map_nil] at eq
    rw [map_eq_nil_iff.mp eq]
  | x :: l₁' =>
    rw [map_cons] at eq
    let ⟨_, _, eq₀, eq₁, eq'⟩ := map_eq_cons_iff.mp eq
    cases eq₀
    rw [finj _ (.head _) _ (.head _) eq₁]
    rw [eq_of_map_eq_map_of_inj eq' fun _ mem₀ _ mem₁ => finj _ (.tail _ mem₀) _ (.tail _ mem₁)]

theorem get!_mem [Inhabited α] {as : List α} (h : i < as.length) : as.get! i ∈ as := by
  rw [get!_eq_getD, getD_eq_getElem?_getD, getElem?_eq, dif_pos h, Option.getD]
  exact getElem_mem _

theorem two_le_count_of_get!_eq_of_ne [BEq α] [LawfulBEq α] [Inhabited α] {as : List α}
  (iltlen : i < as.length) (jltlen : j < as.length) (eq : as.get! i = as.get! j) (ne : i ≠ j)
  : 2 ≤ List.count (as.get! i) as := by match as with
  | [] =>
    rw [length_nil] at iltlen
    nomatch Nat.not_lt_zero _ iltlen
  | a :: as' =>
    rw [count_cons]
    split
    · case isTrue h =>
      by_cases i = 0
      · case pos h =>
        cases h
        rw [eq]
        let ⟨k, eq'⟩ := Nat.exists_eq_succ_of_ne_zero ne.symm
        cases eq'
        rw [get!_cons_succ]
        show 1 + 1 ≤ _
        rw [length_cons] at jltlen
        apply Nat.add_le_add_right <| Nat.succ_le_of_lt <| count_pos_iff.mpr <| get!_mem <|
          Nat.add_lt_add_iff_right.mp jltlen
      · case neg h =>
        let ⟨k, eq'⟩ := Nat.exists_eq_succ_of_ne_zero h
        cases eq'
        rw [get!_cons_succ]
        by_cases j = 0
        · case pos h' =>
          show 1 + 1 ≤ _
          rw [length_cons] at jltlen
          apply Nat.add_le_add_right <| Nat.succ_le_of_lt <| count_pos_iff.mpr <| get!_mem <|
            Nat.add_lt_add_iff_right.mp iltlen
        · case neg h' =>
          apply Nat.le_add_right_of_le
          let ⟨l, eq''⟩ := Nat.exists_eq_succ_of_ne_zero h'
          cases eq''
          exact two_le_count_of_get!_eq_of_ne (Nat.add_lt_add_iff_right.mp iltlen)
            (Nat.add_lt_add_iff_right.mp jltlen) eq (ne <| Nat.succ_inj'.mpr ·)
    · case isFalse h =>
      by_cases i = 0
      · case pos h' =>
        cases h'
        rw [get!_cons_zero, BEq.refl] at h
        nomatch h
      · case neg h' =>
        by_cases j = 0
        · case pos h'' =>
          cases h''
          rw [eq, get!_cons_zero, BEq.refl] at h
          nomatch h
        · case neg h'' =>
          let ⟨k, eq'⟩ := Nat.exists_eq_succ_of_ne_zero h'
          cases eq'
          let ⟨k', eq''⟩ := Nat.exists_eq_succ_of_ne_zero h''
          cases eq''
          rw [get!_cons_succ, Nat.add_zero]
          exact two_le_count_of_get!_eq_of_ne (Nat.add_lt_add_iff_right.mp iltlen)
            (Nat.add_lt_add_iff_right.mp jltlen) eq (ne <| Nat.succ_inj'.mpr ·)

theorem map_eq_id_of_eq_id_of_mem (id_of_mem : ∀ a ∈ as, f a = a) : List.map f as = as := by
  match as with
  | [] => rw [List.map_nil]
  | a :: as' =>
    rw [List.map_cons, id_of_mem _ <| .head _,
        map_eq_id_of_eq_id_of_mem fun _ mem => id_of_mem _ <| .tail _ mem]

theorem sizeOf_map_eq_of_eq_id_of_mem [SizeOf α] {f : α → α}
  (sizeOf_eq_of_mem : ∀ a ∈ as, sizeOf (f a) = sizeOf a) : sizeOf (List.map f as) = sizeOf as := by
  match as with
  | [] => rw [List.map_nil]
  | a :: as' =>
    rw [List.map_cons, List.cons.sizeOf_spec, List.cons.sizeOf_spec, sizeOf_eq_of_mem _ <| .head _,
        sizeOf_map_eq_of_eq_id_of_mem fun _ mem => sizeOf_eq_of_mem _ <| .tail _ mem]

theorem sum_map_eq_of_eq_of_mem {f g : α → Nat} (eq_of_mem : ∀ a ∈ as, f a = g a)
  : (List.map f as).sum = (as.map g).sum := by match as with
  | [] => rw [List.map_nil, List.map_nil]
  | a :: as' =>
    rw [List.map, List.map, List.sum_cons, List.sum_cons, eq_of_mem _ <| .head _,
        sum_map_eq_of_eq_of_mem fun _ mem => eq_of_mem _ <| .tail _ mem]

theorem get!_zip [Inhabited α] [Inhabited β] {l₁ : List α} {l₂ : List β}
  (length_eq : l₁.length = l₂.length) (ilt : i < l₁.length)
  : (zip l₁ l₂).get! i = (l₁.get! i, l₂.get! i) := by match l₁, l₂ with
  | [], _ => nomatch ilt
  | _, [] =>
    rw [length_eq] at ilt
    nomatch ilt
  | a :: l₁', b :: l₂' =>
    rw [zip_cons_cons]
    match i with
    | 0 => rw [get!_cons_zero, get!_cons_zero, get!_cons_zero]
    | i' + 1 =>
      rw [get!_cons_succ, get!_cons_succ, get!_cons_succ]
      rw [length, length] at length_eq
      rw [length] at ilt
      exact get!_zip (Nat.add_one_inj.mp length_eq) <| Nat.lt_of_succ_lt_succ ilt

end List
