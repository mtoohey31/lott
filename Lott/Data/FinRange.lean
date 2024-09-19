namespace Lott.Data

structure FinRange (n : Nat) where
  start := 0
  stop := n
  stopLeStart : start ≤ stop := by simp
  stopLeN : stop ≤ n := by simp

namespace FinRange

def toList (fr : FinRange n) : List (Fin n) := if h : fr.start < fr.stop then
    let h' := Nat.lt_of_lt_of_le h fr.stopLeN
    let stopLeStart := Nat.succ_le_of_lt h
    ⟨fr.start, h'⟩ :: toList { fr with start := fr.start.succ, stopLeStart }
  else
    []

def map (fr : FinRange n) (f : Fin n → α) : List α := fr.toList.map f

macro "[" start:term " : " stop:term "]ᶠ" : term =>
  `({ start := $start, stop := $stop : FinRange $stop })

macro "[" " : " stop:term "]ᶠ" : term => `([0 : $stop]ᶠ)

instance instMembershipFinFinRange : Membership (Fin n) (FinRange n) where
  mem | i, { start, stop, .. } => start ≤ i ∧ i < stop

end FinRange

end Lott.Data
