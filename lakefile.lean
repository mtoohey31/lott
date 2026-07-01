import Lake
import Lake.CLI
import Lean.Elab.Frontend

open Lake DSL

def notex := get_config? notex |>.isSome

-- TODO: Use lib leanOptions for everything instead of args once string escaping is fixed.
def args := if notex then
    #[]
  else
    #[s!"-Dweak.lott.tex.output.dir={get_config? texdir |>.getD (__dir__ |>.toString)}"]

package lott where
  moreGlobalServerArgs := args

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.30.0"

@[default_target]
lean_lib Lott

@[test_driver]
lean_lib LottExamples where
  leanOptions := (if get_config? noterm |>.isSome then #[⟨`lott.term, false⟩] else #[]) ++
    if notex then #[] else #[
      ⟨`weak.lott.tex.locallyNameless, get_config? hideln |>.isNone⟩,
      ⟨`weak.lott.tex.output.sourceRelative, false⟩
    ]
  moreLeanArgs := args

open System

@[implemented_by Lean.enableInitializersExecution]
opaque enableInitializersExecution : IO Unit

inductive Filterable where
  | file (input output : FilePath)
  | dir (path : FilePath)

/--
Filter files containing nonterminal or judgement syntax

USAGE:
  lake run lott-filter <target> <namespace> [<filterable>...]
-/
script «lott-filter» args do
  let spec :: «namespace» :: filterables := args |
    IO.eprintln "USAGE: lake run lott-filter <target> [<filterables>...]"
    return 2
  let currentDir ← IO.currentDir
  let mkAbs name := if FilePath.isAbsolute name then name else FilePath.join currentDir name
  let rec parseFilterables : List String → IO (Except String String)
    | input :: filterables => do
      let isDir ← FilePath.isDir input
      if isDir then
        let rest ← parseFilterables filterables
        return rest.map (s!"#filter {mkAbs input |>.toString.quote}\n" ++ ·)
      let output :: filterables := filterables
        | return .error "no output path following non-directory input"
      let rest ← parseFilterables filterables
      return rest.map
        (s!"#filter {mkAbs input |>.toString.quote} {mkAbs output |>.toString.quote}\n" ++ ·)
    | [] => return .ok ""
  match ← parseFilterables filterables with
  | .error err => do
    IO.eprintln s!"USAGE: lake run lott-filter <target> [<filterables>...]\n{err}"
    return 2
  | .ok inputCommands =>
    let ws ← getWorkspace
    let filter := "Lott.Elab.Filter"
    match ← EIO.toIO' <| parseTargetSpecs ws [filter, spec] with
    | .error cliError =>
      IO.eprintln cliError
      return 1
    | .ok specs =>
      for spec in specs do
        unless spec.buildable do
          IO.eprintln <| CliError.invalidBuildTarget spec.info.key.toSimpleString
          return 1
      ws.runBuild <| buildSpecs specs

      Lean.searchPathRef.set ws.augmentedLeanPath
      enableInitializersExecution

      let input := s!"import {filter}\nimport {spec}\nnamespace {«namespace»}\n" ++
        inputCommands
      let opts := Lean.Options.empty.insert `lott.tex.output.dir <| .ofString "/dev/null"
      let env ← Lean.Elab.runFrontend input opts "LottFilterScript.lean" `LottFilterScript
      return env.isNone.toUInt32
