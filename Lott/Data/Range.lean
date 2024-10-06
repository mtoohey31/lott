namespace Std.Range

def toList (r : Range) : List Nat := if r.step = 0 then
   []
  else if r.start < r.stop then
    r.start :: toList { r with start := r.start + r.step }
  else
    []

instance : Coe Range (List Nat) := ⟨Std.Range.toList⟩

theorem toList_append (h₁ : l ≤ m) (h₂ : m ≤ n) : [l:m] ++ [m:n] = [l:n].toList := by
  rw [toList, if_neg Nat.one_ne_zero]
  split
  · case isTrue h =>
    apply Eq.symm
    rw [toList, if_neg Nat.one_ne_zero]
    apply Eq.symm
    simp only at *
    rw [if_pos (Nat.lt_of_lt_of_le h h₂), List.cons_append, toList_append (Nat.succ_le_of_lt h) h₂]
  · case isFalse h =>
    simp only at *
    have : l = m := match Nat.lt_trichotomy l m with
      | .inl lltm => h lltm |>.elim
      | .inr (.inl leqm) => leqm
      | .inr (.inr mltn) => Nat.not_lt_of_le h₁ mltn |>.elim
    rw [this, List.nil_append]
termination_by m - l
decreasing_by
  all_goals simp_wf
  apply Nat.sub_succ_lt_self
  assumption

theorem toList_eq_nil_of_stop_le_start (h : r.stop ≤ r.start) : toList r = [] := by
  rw [toList]
  split
  · case isTrue => rfl
  · case isFalse => rw [if_neg (Nat.not_lt_of_le h)]

theorem map_eq_of_eq_of_mem {f g : Nat → α} (h : ∀ i ∈ [m:n], f i = g i)
  : List.map (fun i => f i) [m:n] = List.map (fun i => g i) [m:n] := by
  rw [toList]
  split
  · case isTrue =>
    contradiction
  · case isFalse =>
    split
    · case isTrue => contradiction
    · case isFalse =>
      split
      · case isTrue h' =>
        simp only [List.map] at *
        let h'' i (mem : i ∈ [m + 1:n]) := h i ⟨Nat.le_of_succ_le mem.lower, mem.upper⟩
        rw [h m ⟨Nat.le_refl _, h'⟩, map_eq_of_eq_of_mem (m := m + 1) h'']
      · case isFalse h => rfl
termination_by n - m
decreasing_by
  all_goals simp_wf
  apply Nat.sub_succ_lt_self
  assumption

theorem map_eq_of_eq_of_mem' {f g : Nat → α} (h : ∀ i ∈ [m:n], f i = g i)
  : List.map (fun i => f i) (Coe.coe [m:n]) = List.map (fun i => g i) (Coe.coe [m:n]) := by
  dsimp [Coe.coe]
  exact map_eq_of_eq_of_mem h

theorem mem_of_mem_map {f : Nat → α} (h : x ∈ List.map (fun i => f i) [m:n])
  : ∃ i ∈ [m:n], x = f i := by
  rw [toList, if_neg Nat.one_ne_zero] at h
  split at h
  · case isTrue h' =>
    rw [List.map] at h
    cases h
    · case head => exact .intro m ⟨⟨Nat.le_refl _, h'⟩, rfl⟩
    · case tail h'' =>
      have ⟨i, mem, eq⟩ := mem_of_mem_map (m := m + 1) h''
      exact ⟨i, ⟨Nat.le_of_succ_le mem.lower, mem.upper⟩, eq⟩
  · case isFalse h' => cases h
termination_by n - m
decreasing_by
  all_goals simp_wf
  apply Nat.sub_succ_lt_self
  assumption

theorem map_shift {f : Nat → α} (h : j ≤ m)
  : List.map (fun i => f (i + j)) [m - j:n - j] = List.map (fun i => f i) [m:n] := by
  rw [toList]
  apply Eq.symm
  rw [toList]
  apply Eq.symm
  rw [if_neg Nat.one_ne_zero, if_neg Nat.one_ne_zero]
  simp only
  split
  · case isTrue h' =>
    rw [if_pos, List.map, Nat.sub_add_cancel h, ← Nat.sub_add_comm h, map_shift (m := m + 1),
        ← List.map]
    · exact Nat.le_succ_of_le h
    · have := Nat.sub_pos_of_lt h'
      rw [Nat.sub_right_comm, Nat.sub_sub, Nat.sub_add_cancel h] at this
      exact Nat.lt_of_sub_pos this
  · case isFalse h' =>
    rw [List.map, if_neg, List.map]
    intro h''
    apply h'
    have := Nat.sub_pos_of_lt h''
    rw [← Nat.sub_add_cancel h, ← Nat.sub_sub, ← Nat.sub_right_comm] at this
    exact Nat.lt_of_sub_pos this

theorem map_append {f : Nat → α} (h₁ : l ≤ m) (h₂ : m ≤ n)
  : List.map f [l:m] ++ List.map f [m:n] = List.map f [l:n] := by
  rw [← List.map_append, toList_append h₁ h₂]

end Std.Range
