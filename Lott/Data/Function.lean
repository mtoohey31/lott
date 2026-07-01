module

@[expose]
public
def Function.Injective' (f : α → β) : Prop := ∀ x y, f x = f y → x = y
