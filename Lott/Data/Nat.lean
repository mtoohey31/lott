namespace Nat

theorem eq_of_beq_eq_true' {a b : Nat} (h : (a == b) = true) : a = b := by
  dsimp [BEq.beq, decide, instDecidableEqNat, Nat.decEq] at h
  split at h
  · case _ h' => exact Nat.eq_of_beq_eq_true h'
  · case _ h' => nomatch h

end Nat
