namespace Option

def someIf (x : α) (b : Bool) : Option α := if b then some x else none

theorem someIf_true : someIf x true = some x := rfl

theorem eq_of_someIf_eq_some : someIf x b = some y → x = y ∧ b = true := by
  intro eq
  rw [someIf] at eq
  split at eq
  · case isTrue h => exact ⟨some.inj eq, h⟩
  · case isFalse => nomatch eq

def keepIf (x : Option α) (b : Bool) : Option α := if b then x else none

def mapMem (a? : Option α) (f : (a : α) → a ∈ a? → β) : Option β := match a? with
  | some a => f a rfl
  | none => none

theorem mapMem_eq_map {a? : Option α} : a?.mapMem (fun a _ => f a) = a?.map f := by cases a? <;> rfl

end Option
