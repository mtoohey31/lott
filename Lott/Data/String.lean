module

namespace String

def toPascalParts (s : String) : Array String := Id.run do
  let rawParts := s.toList.splitBy (·.isUpper == ·.isUpper)
  let mut parts : Array String := #[]
  for rawPart in rawParts do
    if rawPart[0]!.isLower then
      if let some last := parts.back? then
        parts := parts.pop.push <| last ++ String.ofList rawPart
      else
        parts := parts.push <| .ofList rawPart
      continue

    if rawPart.length > 1 then
      parts := parts ++ #[.ofList rawPart.dropLast, rawPart.getLast!.toString]
    else
      parts := parts.push <| .ofList rawPart
  return parts

def pascalToSnake (s : String) : String :=
  "_".intercalate <| s.toPascalParts.toList.map String.toLower

def pascalToTitle (s : String) : String := " ".intercalate s.toPascalParts.toList

public def texEscape (s : String) : String :=
  join <| s.toList.map fun
    | c@'&' | c@'%' | c@'$' | c@'#' | c@'_' | c@'{' | c@'}' => "\\" ++ c.toString
    | '~' => "\\textasciitilde"
    | '^' => "\\textasciicircum"
    | '\\' => "\\textbackslash"
    | '«' | '»' => ""
    | c => c.toString

/-
Based on `munge` in libcpp/mkdeps.cc from the GCC source code. This is
imperfect as some special characters can't be escaped.
-/
def makeEscape (s : String) : String := Id.run do
  let mut res := ""
  let mut slashes := 0
  for c in s.toList do
    match c with
    | '\\' => slashes := slashes + 1
    | '$' =>
      res := res.push '$'
      slashes := 0
    | ':' =>
      res := res.push '\\'
      slashes := 0
    | ' ' | '\t' =>
      /-
      `munge`'s source contains a comment here that says: "A
      space or tab preceded by 2N+1 backslashes represents N
      backslashes followed by space..."
      -/
      res := res.pushn '\\' <| slashes + 1
      slashes := 0
    | '#' =>
      res := res.push '\\'
      slashes := 0
    | _ => slashes := 0
    res := res.push c
  res

partial def Slice.dropPrefixes (s pre : Slice) : Slice := match s.dropPrefix? pre with
  | some s' => s'.dropPrefixes pre
  | none => s

def dropPrefixes (s pre : String) : Slice := s.toSlice.dropPrefixes pre

end String
