partial
def Substring.dropPrefixes (s pre : Substring) : Substring :=
  if pre.bsize = 0 then
    s
  else
    match s.dropPrefix? pre with
    | some s' => s'.dropPrefixes pre
    | none => s
