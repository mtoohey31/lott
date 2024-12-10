theorem sizeOf_fst_lt_of_prod_mem [SizeOf α] {as : List (α × α)} (h : (a, b) ∈ as) : sizeOf a < sizeOf as := by
  apply Nat.lt_trans
  · show sizeOf a < sizeOf (a, b)
    rw [Prod.mk.sizeOf_spec]
    apply Nat.lt_add_right
    rw [Nat.add_comm]
    exact Nat.lt_succ_self _
  · exact List.sizeOf_lt_of_mem h

macro_rules
  | `(tactic| decreasing_trivial) => `(tactic| first
    | with_reducible
        apply Nat.lt_of_lt_of_le (sizeOf_fst_lt_of_prod_mem ?h)
        case h => assumption
      simp_arith)

theorem sizeOf_snd_lt_of_prod_mem [SizeOf α] {as : List (α × α)} (h : (a, b) ∈ as) : sizeOf b < sizeOf as := by
  apply Nat.lt_trans
  · show sizeOf b < sizeOf (a, b)
    rw [Prod.mk.sizeOf_spec]
    apply Nat.lt_add_left_iff_pos.mpr
    rw [Nat.add_comm]
    exact Nat.succ_pos _
  · exact List.sizeOf_lt_of_mem h

macro_rules
  | `(tactic| decreasing_trivial) => `(tactic| first
    | with_reducible
        apply Nat.lt_of_lt_of_le (sizeOf_snd_lt_of_prod_mem ?h)
        case h => assumption
      simp_arith)
