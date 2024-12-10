namespace Option

def mapMem (a? : Option α) (f : (a : α) → a ∈ a? → β) : Option β := match a? with
  | some a => f a rfl
  | none => none

theorem mapMem_eq_map {a? : Option α} : a?.mapMem (fun a _ => f a) = a?.map f := by cases a? <;> rfl

end Option
