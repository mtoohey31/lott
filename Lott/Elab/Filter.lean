import Lott.Elab.Basic
import Lott.Parser

namespace Lott

open Lean
open Lean.Parser
open Lean.Elab.Command
open System
open IO.FS

elab_rules : command
  | `(#filter $inputName:str $[$outputName?:str]?) => do
    if !(← getTexOutputSome) then
      throwError "can't #filter when when lott.tex.output.dir is unset"

    let some parent := FilePath.parent <| ← getFileName
      | throwError "failed to resolve parent of current file"
    let input ← readFile <| parent / inputName.getString

    let s := mkParserState input
    let ictx := mkInputContext input inputName.getString
    let env ← getEnv
    let s := filterParserFn.run ictx { env, options := {} } (getTokenTable env) s
    if !s.allErrors.isEmpty then
      throwError s.toErrorMsg ictx
    else if !ictx.input.atEnd s.pos then
      throwError s.mkError "end of input" |>.toErrorMsg ictx

    let output ← s.stxStack.toSubarray.toArray.filterMapM fun
      | .node _ `Lott.NonEmbed #[.atom _ s] => return s
      | stx => do
        let s ← liftTermElabM <| texElabSymbolOrJudgement stx.getKind inputName stx
        return "$" ++ s ++ "$"

    let some outputName := outputName?.map TSyntax.getString |>.orElse
      fun () => inputName.getString.dropSuffix? ".lotttmpl" |>.map Substring.toString
      | throwErrorAt inputName
          "#filter input name must end with '.lotttmpl' if output name is omitted"
    let outputName := parent / outputName

    -- TODO: Make the output path here relative if possible. Needs diff_paths-like.
    writeMakeDeps outputName (extraDeps := [parent / inputName.getString])
    liftIO <| writeFile outputName <| String.join output.toList

end Lott
