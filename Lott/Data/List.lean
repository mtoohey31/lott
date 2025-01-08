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

theorem le_sum_of_mem {as : List Nat} (h : a ∈ as) : a ≤ as.sum := by
  match h with
  | .head _ =>
    rw [sum_cons]
    exact Nat.le_add_right _ _
  | .tail _ h' =>
    rw [sum_cons]
    exact Nat.le_trans (Nat.le_add_left ..) <| Nat.add_le_add_iff_left.mpr <| le_sum_of_mem h'

end List
