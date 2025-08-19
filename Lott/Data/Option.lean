namespace Option

def someIf (x : α) (b : Bool) : Option α := if b then some x else none

theorem someIf_true : someIf x true = some x := rfl

theorem someIf_false : someIf x false = none := rfl

theorem someIf_get!_eq [Inhabited α] {x? : Option α} : someIf (get! x?) (isSome x?) = x? := by
  match x? with
  | some _ => rw [get!, isSome, someIf_true]
  | none => rw [isSome, someIf_false]

theorem eq_of_someIf_eq_some : someIf x b = some y → x = y ∧ b = true := by
  intro eq
  rw [someIf] at eq
  split at eq
  · case isTrue h => exact ⟨some.inj eq, h⟩
  · case isFalse => nomatch eq

theorem eq_of_someIf_eq_none : someIf x b = none → b = false := by
  intro eq
  rw [someIf] at eq
  split at eq
  · case isTrue => nomatch eq
  · case isFalse h => exact Bool.not_eq_true _ |>.mp h

theorem someIf_eq : someIf x b₀ = someIf y b₁ → b₀ = b₁ := by
  intro h
  match b₁ with
  | true => exact eq_of_someIf_eq_some h |>.right
  | false => exact eq_of_someIf_eq_none h

theorem isSome_someIf : isSome (someIf x b) = b := by
  rw [someIf]
  split
  · case isTrue h =>
    cases h
    rw [isSome]
  · case isFalse h =>
    rw [Bool.not_eq_true _ |>.mp h, isSome]

def keepIf (x : Option α) (b : Bool) : Option α := if b then x else none

def mapMem (a? : Option α) (f : (a : α) → a ∈ a? → β) : Option β := match a? with
  | some a => f a rfl
  | none => none

theorem mapMem_eq_map {a? : Option α} : a?.mapMem (fun a _ => f a) = a?.map f := by cases a? <;> rfl

end Option
