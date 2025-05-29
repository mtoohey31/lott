import Lott.Elab.Basic
import Lott.Parser.Filter

namespace Lott

open Lean
open Lean.Parser
open Lean.Elab.Command
open System FilePath
open IO.FS

private
def mkAbsolute (name : String) : CommandElabM FilePath := do
  if isAbsolute name then
    return name
  let some parent := parent <| ← getFileName |
    throwError "failed to resolve parent of current file"
  return parent / name

elab_rules : command
  | `(#filter $inputName:str $[$outputName?:str]?) => do
    if !(← getTexOutputSome) then
      throwError "can't #filter when when lott.tex.output.dir is unset"

    let inputPath ← mkAbsolute inputName.getString
    if ← isDir inputPath then
      if let some outputName := outputName? then
        throwErrorAt outputName "#filter output cannot be specified when input is a directory"

      let mut failed := false

      for entry in ← readDir inputPath do
        if extension entry.path != some "lottinput" then
          continue

        let input ← String.trimRight <$> readFile entry.path

        let s := mkParserState input
        let ictx := mkInputContext input entry.path.toString
        let env ← getEnv
        let parserFn := orelseFn
          (orelseFn
            (atomicFn (andthenFn qualifiedSymbolParser.fn whitespace))
            (atomicFn (andthenFn (withPosition (categoryParser `Lott.Judgement 0)).fn whitespace)))
          (andthenFn (withPosition (categoryParser `Lott.Symbol 0)).fn whitespace)
        let s := parserFn.run ictx { env, options := {} } (getTokenTable env) s
        if !s.allErrors.isEmpty then
          logWarning s!"parse failure for `{input}` in {entry.fileName}: {s.toErrorMsg ictx}"
          failed := true
          continue
        else if !ictx.input.atEnd s.pos then
          let msg := s.mkError "end of input" |>.toErrorMsg ictx
          logWarning s!"parse failure for `{input}` in {entry.fileName}: {msg}"
          failed := true
          continue

        let mut stx := s.stxStack.back
        if stx.getKind == choiceKind then
          let possibilities := ", ".intercalate <| stx.getArgs.map (·.getKind.toString) |>.toList
          logWarning s!"`{input}` from {entry.fileName} is ambiguous between: {possibilities}"
          failed := true
          continue
        if stx.getKind == `Lott.QualifiedSymbol then
          stx := stx.getArg 2

        let output ← liftTermElabM <| texElabSymbolOrJudgement stx.getKind default inputName stx
        writeFile (withExtension entry.path "tex") <| output ++ "\n"

      if failed then
        throwError "some inputs were not processed succesfully"
      return

    let outputPath ← if let some outputName := outputName? then
        mkAbsolute outputName.getString
      else
        let some outputName := outputName?.map TSyntax.getString |>.orElse
          fun () => inputName.getString.dropSuffix? ".lotttmpl" |>.map Substring.toString
          | throwErrorAt inputName
              "#filter input name must end with '.lotttmpl' if output name is omitted"

        mkAbsolute outputName

    let input ← readFile inputPath

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
        let s ← liftTermElabM <| texElabSymbolOrJudgement stx.getKind default inputName stx
        return "$" ++ s ++ "$"

    -- TODO: Make the output path here relative if possible. Needs diff_paths-like.
    writeMakeDeps outputPath (extraDeps := [inputPath])
    writeFile outputPath <| String.join output.toList

end Lott
