import Lean.Data.Name

import Lott.Data.Option

namespace Lean.Name

def getFinal : Name → Name
  | anonymous => anonymous
  | str _ s => str anonymous s
  | num _ n => num anonymous n

def erasePrefix? : Name → Name → Option Name
  | anonymous, pf => .someIf anonymous (anonymous == pf)
  | name@(str pre s), pf => do
    if name == pf then
      return anonymous

    let pre' ← pre.erasePrefix? pf
    return str pre' s
  | name@(num pre n), pf => do
    if name == pf then
      return anonymous

    let pre' ← pre.erasePrefix? pf
    return num pre' n

inductive Component where
  | str (s : String)
  | num (n : Nat)
deriving BEq

def fromComponents' : List Name → Name
  | [] => anonymous
  | anonymous :: cs => fromComponents' cs
  | c@(str ..) :: cs => c ++ fromComponents' cs
  | c@(num ..) :: cs => c ++ fromComponents' cs

def removeCommonPrefixes (n₀ n₁ : Name) : Name × Name :=
  let cs₀ := n₀.components
  let cs₁ := n₁.components
  let sameCount := cs₀.zipWithAll (fun c₀? c₁? => c₀? == c₁?) cs₁ |>.takeWhile id |>.length
  let sameCount := if sameCount == cs₀.length || sameCount == cs₁.length then
      sameCount - 1
    else
      sameCount
  (fromComponents' <| cs₀.drop sameCount, fromComponents' <| cs₁.drop sameCount)

end Lean.Name
