namespace Std.Range

def toList (range : Range) : List Nat :=
  let rec loop (fuel i stop step : Nat) : List Nat :=
    if i ≥ stop then
      []
    else match fuel with
     | 0 => []
     | fuel + 1 => i :: loop fuel (i + step) stop step
  loop range.stop range.start range.stop range.step

instance : Coe Range (List Nat) := ⟨Std.Range.toList⟩

end Std.Range
