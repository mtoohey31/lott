namespace List

theorem map_singleton_join (xs : List α) : (xs.map fun x => [f x]).flatten = xs.map f :=
  match xs with
  | [] => rfl
  | x :: xs' => by rw [List.map, List.map, List.flatten, List.singleton_append, xs'.map_singleton_join]

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

end List
