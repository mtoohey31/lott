import Lott.Data.Nat

namespace Std.Range

def toList (r : Range) : List Nat := if r.start < r.stop then
    r.start :: toList { r with start := r.start + r.step }
  else
    []
termination_by r.stop - r.start
decreasing_by
  apply Nat.sub_lt_sub_left _ <| Nat.lt_add_of_pos_right r.step_pos
  assumption

instance : Coe Range (List Nat) := ⟨Std.Range.toList⟩

abbrev map (r : Range) (f : Nat → α) : List α := r.toList.map f

abbrev flatMap (r : Range) (f : Nat → List α) : List α := r.toList.flatMap f

theorem toList_append (h₁ : l ≤ m) (h₂ : m ≤ n) : [l:m] ++ [m:n] = [l:n].toList := by
  rw [toList]
  split
  · case isTrue h =>
    apply Eq.symm
    rw [toList]
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

theorem toList_eq_nil_iff : toList [m:n] = [] ↔ n ≤ m where
  mp eq := by
    rw [toList] at eq
    split at eq
    · case isTrue h => nomatch eq
    · case isFalse h => exact Nat.le_of_not_lt h
  mpr le := by rw [toList, if_neg (Nat.not_lt_of_le le)]

theorem mem_of_mem_toList (h : i ∈ [m:n].toList) : i ∈ [m:n] := by
  rw [toList] at h
  split at h
  · case isTrue mltn =>
    cases h
    · case head => exact ⟨Nat.le_refl _, mltn, Nat.mod_one _⟩
    · case tail h' =>
      let ⟨msucclei, iltn, _⟩ := mem_of_mem_toList h'
      exact ⟨Nat.le_of_succ_le msucclei, iltn, Nat.mod_one _⟩
  · case isFalse =>
    nomatch h
termination_by n - m
decreasing_by
  all_goals simp_arith
  apply Nat.sub_succ_lt_self
  assumption

theorem map_eq_of_eq_of_mem {f g : Nat → α} (h : ∀ i ∈ [m:n], f i = g i)
  : List.map (fun i => f i) [m:n] = List.map (fun i => g i) [m:n] :=
  List.map_eq_map_iff.mpr (h · <| mem_of_mem_toList ·)

theorem map_eq_of_eq_of_mem' {f g : Nat → α} (h : ∀ i ∈ [m:n], f i = g i)
  : List.map (fun i => f i) (Coe.coe [m:n]) = List.map (fun i => g i) (Coe.coe [m:n]) := by
  dsimp [Coe.coe]
  exact map_eq_of_eq_of_mem h

theorem map_eq_of_eq_of_mem'' {f g : Nat → α} (h : ∀ i ∈ [m:n], f i = g i)
  : [m:n].map (fun i => f i) = [m:n].map (fun i => g i) := by exact map_eq_of_eq_of_mem h

theorem eq_of_mem_of_map_eq {f g : Nat → α}
  (h : List.map (fun i => f i) [m:n] = List.map (fun i => g i) [m:n]) : ∀ i ∈ [m:n], f i = g i := by
  intro i ⟨mlei, iltn, _⟩
  let mltn := Nat.lt_of_le_of_lt mlei iltn
  rw [toList, if_pos mltn] at h
  rw [List.map, List.map] at h
  simp only at h
  by_cases m = i
  · case pos h' =>
    cases h'
    exact List.cons_eq_cons.mp h |>.left
  · case neg h' =>
    exact eq_of_mem_of_map_eq (List.cons_eq_cons.mp h |>.right) i
      ⟨Nat.succ_le_of_lt <| Nat.lt_of_le_of_ne mlei h', iltn, Nat.mod_one _⟩
termination_by n - m
decreasing_by
  all_goals simp_wf
  apply Nat.sub_succ_lt_self
  assumption

theorem eq_of_mem_of_map_eq' {f g : Nat → α}
  (h : List.map (fun i => f i) (Coe.coe [m:n]) = List.map (fun i => g i) (Coe.coe [m:n]))
  : ∀ i ∈ [m:n], f i = g i := by
  dsimp [Coe.coe] at h
  exact eq_of_mem_of_map_eq h

theorem mem_of_mem_map {f : Nat → α} (h : x ∈ List.map (fun i => f i) [m:n])
  : ∃ i ∈ [m:n], x = f i := by
  rw [toList] at h
  split at h
  · case isTrue h' =>
    rw [List.map] at h
    cases h
    · case head => exact .intro m ⟨⟨Nat.le_refl _, h', Nat.mod_one _⟩, rfl⟩
    · case tail h'' =>
      have ⟨i, mem, eq⟩ := mem_of_mem_map (m := m + 1) h''
      exact ⟨i, ⟨Nat.le_of_succ_le mem.lower, mem.upper, Nat.mod_one _⟩, eq⟩
  · case isFalse h' => cases h
termination_by n - m
decreasing_by
  all_goals simp_wf
  apply Nat.sub_succ_lt_self
  assumption

theorem mem_map_of_mem (h : i ∈ [m:n]) : f i ∈ List.map f [m:n] := by
  rw [toList]
  split
  · case isTrue h' =>
    simp only
    rw [List.map]
    by_cases i = m
    · case pos h'' =>
      cases h''
      exact .head _
    · case neg h'' =>
      exact .tail _ <| mem_map_of_mem ⟨
        Nat.succ_le_of_lt <| Nat.lt_of_le_of_ne h.lower (Ne.symm h''),
        h.upper,
        Nat.mod_one _
      ⟩
  · case isFalse h' => exact h' (Nat.lt_of_le_of_lt h.lower h.upper) |>.elim
termination_by i - m
decreasing_by
  all_goals simp_wf
  apply Nat.sub_add_lt_sub _ Nat.one_pos
  apply Nat.succ_le_of_lt
  apply Nat.lt_of_le_of_ne h.lower
  apply Ne.symm
  assumption

theorem map_shift {f : Nat → α} (h : j ≤ m)
  : [m - j:n - j].map (fun i => f (i + j)) = [m:n].map fun i => f i := by
  rw [map, map, toList]
  apply Eq.symm
  rw [toList]
  apply Eq.symm
  simp only
  split
  · case isTrue h' =>
    rw [if_pos, List.map, Nat.sub_add_cancel h, ← Nat.sub_add_comm h, ← map, map_shift (m := m + 1),
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

theorem map_shift' {f : Nat → α}
  : [m:n].map (fun i => f i) = [m + j:n + j].map fun i => f (i - j) := by
  rw [map, map, toList]
  apply Eq.symm
  rw [toList]
  apply Eq.symm
  simp only
  split
  · case isTrue h' =>
    rw [if_pos <| Nat.add_lt_add_right h' _, List.map_cons, List.map_cons, Nat.add_sub_self_right,
        Nat.add_assoc, Nat.add_comm j 1, ← Nat.add_assoc, ← map, ← map, map_shift']
  · case isFalse h' =>
    rw [List.map_nil, if_neg <| Nat.not_lt_of_le <| Nat.add_le_add_right (Nat.le_of_not_lt h') _,
        List.map_nil]

theorem map_append {f : Nat → α} (h₁ : l ≤ m) (h₂ : m ≤ n)
  : List.map f [l:m] ++ List.map f [m:n] = List.map f [l:n] := by
  rw [← List.map_append, toList_append h₁ h₂]

theorem length_toList : [m:n].toList.length = n - m := by
  rw [toList]
  split
  · case isTrue h =>
    simp only
    rw [List.length_cons, length_toList, Nat.sub_add_eq, Nat.sub_add_cancel]
    exact Nat.succ_le_of_lt <| Nat.sub_pos_iff_lt.mpr h
  · case isFalse h => rw [List.length_nil, Nat.sub_eq_zero_of_le <| Nat.le_of_not_lt h]
termination_by n - m
decreasing_by
  all_goals simp_arith
  apply Nat.sub_succ_lt_self
  assumption

theorem map_get!_eq [Inhabited α] {as : List α} : [:as.length].map as.get! = as := by
  match as with
  | [] =>
    rw [List.length_nil, map, toList, if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map_nil]
  | a :: as' =>
    rw [List.length_cons, map, toList, if_pos (Nat.succ_pos _), List.map_cons, List.get!_cons_zero,
        ← map, ← map_shift (Nat.le_add_left ..), Nat.add_sub_cancel, Nat.add_sub_cancel,
        map_eq_of_eq_of_mem'' fun _ _ => List.get!_cons_succ .., map_get!_eq]

theorem count_toList_le_one : [m:n].toList.count l ≤ 1 := by
  rw [toList]
  split
  · case isTrue h =>
    rw [List.count_cons]
    simp only
    split
    · case isTrue h' =>
      cases Nat.eq_of_beq_eq_true' h'
      rw [List.count_eq_zero_of_not_mem]
      · exact Nat.le_refl _
      · intro lmem
        nomatch Nat.ne_of_lt <| Nat.lt_of_succ_le <| And.left <| mem_of_mem_toList lmem
    · case isFalse h' =>
      rw [Nat.add_zero]
      exact count_toList_le_one
  · case isFalse h =>
    rw [List.count_nil]
    exact Nat.le_of_lt Nat.one_pos
termination_by n - m
decreasing_by
  all_goals simp_arith
  apply Nat.sub_succ_lt_self
  assumption

theorem get!_map [Inhabited α] {f : Nat → α} (iltnsubm : i < n - m)
  : ([m:n].map f).get! i = f (i + m) := by match i with
  | 0 =>
    rw [map, toList, if_pos (Nat.lt_of_sub_pos iltnsubm), List.map_cons, List.get!_cons_zero,
        Nat.zero_add]
  | i' + 1 =>
    let mltn := Nat.lt_of_sub_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) iltnsubm)
    rw [map, toList, if_pos mltn, List.map_cons, List.get!_cons_succ, ← map,
        ← map_shift (j := 1) (Nat.succ_le_of_lt (Nat.add_one_pos _)), get!_map, Nat.add_sub_cancel,
        Nat.add_assoc, Nat.add_comm m, ← Nat.add_assoc]
    rw [Nat.add_sub_cancel, Nat.sub_right_comm]
    apply Nat.lt_sub_of_add_lt
    exact iltnsubm

theorem skolem [Inhabited α] {p : Nat → α → Prop}
  : (∀ i ∈ [:n], ∃ a, p i a) → ∃ f : Nat → α, ∀ i ∈ [:n], p i (f i) := by
  intro h
  induction n with
  | zero => exact ⟨fun _ => default, nofun⟩
  | succ n ih =>
    let ⟨f', h'⟩ := ih fun i mem => h i ⟨mem.lower, Nat.lt_add_right _ mem.upper, Nat.mod_one _⟩
    let ⟨a, h''⟩ := h n ⟨Nat.zero_le _, Nat.lt_succ_self _, Nat.mod_one _⟩
    let f i := if i = n then a else f' i
    apply Exists.intro f
    intro i mem
    dsimp only [f]
    split
    · case isTrue h''' =>
      cases h'''
      exact h''
    · case isFalse h''' =>
      exact h' i ⟨mem.lower, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ mem.upper) h''', Nat.mod_one _⟩

theorem mem_zip_map {f : Nat → α} {g : Nat → β}
  : x ∈ ([m:n].map f).zip ([m:n].map g) → ∃ i ∈ [m:n], x = (f i, g i) := by
  intro mem
  rw [map, map, toList] at mem
  split at mem
  case isFalse h => nomatch mem
  case isTrue h =>
  rw [List.map_cons, List.map_cons, List.zip_cons_cons] at mem
  cases mem with
  | head => exact ⟨m, ⟨Nat.le.refl, h, Nat.mod_one _⟩, rfl⟩
  | tail _ mem' =>
    let ⟨i, imem, eq⟩ := mem_zip_map mem'
    simp at *
    exact ⟨i, ⟨Nat.le_trans Nat.le.refl.step imem.lower, imem.upper, Nat.mod_one _⟩, eq⟩
termination_by n - m
decreasing_by
  all_goals simp_arith
  apply Nat.sub_succ_lt_self
  assumption

theorem map_eq_cons_of_lt (mltn : m < n) : [m:n].map f = f m :: [m+1:n].map f := by
  rw [map, toList, if_pos mltn, List.map_cons, ← map]

theorem map_same_eq_nil : [n:n].map f = [] := by
  rw [map, toList, if_neg <| Nat.not_lt_of_le Nat.le.refl, List.map_nil]

theorem map_eq_snoc_of_lt (mltn : m < n) : [m:n].map f = [m:n - 1].map f ++ [f (n - 1)] := by
  let npos := Nat.lt_of_le_of_lt (Nat.zero_le _) mltn
  rw [map, ← map_append (l := m) (m := n - 1) (n := n) (Nat.le_sub_one_of_lt mltn) (Nat.sub_le _ _),
      ← map, ← map, map_eq_cons_of_lt <| Nat.sub_lt npos Nat.one_pos, Nat.sub_add_cancel npos,
      map_same_eq_nil]

end Std.Range
