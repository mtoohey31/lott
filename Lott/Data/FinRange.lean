namespace Lott.Data

structure FinRange (n : Nat) where
  start := 0
  stop := n
  stopLe : stop ≤ n := by simp

macro "[" start:term " : " stop:term "]ᶠ" : term =>
  `({ start := $start, stop := $stop : FinRange $stop })

macro "[" " : " stop:term "]ᶠ" : term => `([0 : $stop]ᶠ)

instance instMembershipFinFinRange : Membership (Fin n) (FinRange n) where
  mem | i, { start, stop, .. } => start ≤ i ∧ i < stop

end Lott.Data
