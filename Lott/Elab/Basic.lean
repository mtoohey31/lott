import Lott.Data.Char
import Lott.Data.List
import Lott.Data.Name
import Lott.Data.Option
import Lott.Data.String
import Lott.Elab.NoTexJudgement
import Lott.Environment
import Lott.Parser
import Lott.IR

-- TODO: Remove unnecessary qualifications from names.
-- TODO: Delab to embeddings when possible.
-- TODO: Make hover in non-terminal work right.
-- TODO: Test stuff without locally nameless.
-- TODO: Centralize validation of bind/id usage in nonterminals.

namespace Lott

open IO.FS
open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Syntax
open Lean.Parser
open Lean.Parser.Command
open Lean.Parser.Syntax
open Lean.Parser.Term
open Lott.IR
open System

/- Utility stuff. -/

register_option lott.tex.locallyNameless : Bool := {
  defValue := true
  descr := "show locally nameless operations in tex output"
}

register_option lott.tex.output.dir : String := {
  defValue := "."
  descr := "directory where tex output files should be saved"
}

register_option lott.tex.output.sourceRelative : Bool := {
  defValue := true
  descr := "when output.dir is relative, whether it should be considered relative to the source file's parent, or to the Lean process's working directory"
}

register_option lott.tex.output.makeDeps : Bool := {
  defValue := false
  descr := "also output .d files for make alongside tex"
}

private
def writeMakeDeps (filePath : FilePath) : CommandElabM Unit := do
  if !(← getOptions).get lott.tex.output.makeDeps.name lott.tex.output.makeDeps.defValue then
    return

  let sp ← liftIO <| initSrcSearchPath
  let depPaths ← (← getEnv).allImportedModuleNames.mapM (findLean sp ·)
  let deps := " ".intercalate <| depPaths.toList.map
    (·.toString.dropPrefixes "./" |>.toString)
  writeFile (filePath.addExtension "d")
    s!"{filePath.toString.dropPrefixes "./" |>.toString}: {deps}\n"

private
def writeTexOutput (name : Name) (mkTex : CommandElabM String) : CommandElabM Unit := do
  let opts ← getOptions
  let some (outputDir : String) := opts.get? lott.tex.output.dir.name | return
  let outputDir ← if FilePath.isAbsolute outputDir then
      pure (outputDir : FilePath)
    else if opts.get lott.tex.output.sourceRelative.name lott.tex.output.sourceRelative.defValue then
      let some parent := FilePath.parent <| ← getFileName
        | throwError "failed to resolve parent of current file"
      pure <| parent / outputDir
    else
      pure outputDir
  let outputName := outputDir / name.toStringWithSep "/" false |>.addExtension "tex"
  let some parent := outputName.parent | throwError "failed to resolve parent of output file name"
  createDirAll parent

  writeMakeDeps outputName
  writeFile outputName <| ← mkTex

abbrev TexElab := (ref : Syntax) → Syntax → TermElabM String

private unsafe
def mkLottTexElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute TexElab) := do
  mkElabAttribute TexElab .anonymous `lott_tex_elab `Lott ``Lott.TexElab "lott" ref

@[implemented_by mkLottTexElabAttributeUnsafe]
opaque mkLottTexElabAttribute (ref : Name) : IO (KeyedDeclsAttribute TexElab)

initialize lottTexElabAttribute : KeyedDeclsAttribute TexElab ← mkLottTexElabAttribute decl_name%

private
def texElabIdx : Syntax → TermElabM String
  | .ident _ _ val _ => pure <| val.toString false |>.texEscape
  | .node _ `num #[.atom _ raw] => pure raw.texEscape
  | _ => throwUnsupportedSyntax

private
def texElabMetavar : TexElab := fun
  | _, .node _ _ #[.ident _ _ val _]
  | _, .node _ _ #[.ident _ _ val _, .atom _ "$", .node _ `num _] =>
    return val.toString false |>.texEscape
  | ref, .node _ _ #[«fun», .atom _ "@", idx] => do
    let funTex ← texElabMetavar ref «fun»
    let idxTex ← texElabIdx idx
    return s!"\{{funTex}}_\{{idxTex}}"
  | _, _ => throwUnsupportedSyntax

mutual

private
def texElabVariable : TexElab := fun
  | _, .node _ _ #[.node _ _ #[.ident _ _ val _] ] => return val.toString false |>.texEscape
  | ref, .node info kind #[.node _ _ #[«fun», .atom _ "@", idx] ] => do
    let funTex ← texElabVariable ref <| .node info kind #[«fun»]
    let idxTex ← texElabIdx idx
    return s!"\{{funTex}}_\{{idxTex}}"
  | ref, .node _ catName #[
      base@(.node _ catName₀ _),
      .atom _ "[",
      val@(.node _ symbolPrefixedValName _),
      .atom _ "/",
      var@(.node _ symbolPrefixedVarName _),
      .atom _ "]"
    ] => do
    if catName != catName₀ then
      throwUnsupportedSyntax

    if !symbolPrefix.isPrefixOf catName then throwUnsupportedSyntax
    if !symbolPrefix.isPrefixOf symbolPrefixedValName then throwUnsupportedSyntax
    if !symbolPrefix.isPrefixOf symbolPrefixedVarName then throwUnsupportedSyntax

    let baseTex ← texElabSymbolOrJudgement catName ref base
    let valTex ← texElabSymbolOrJudgement symbolPrefixedValName ref val
    let varTex ← texElabSymbolOrJudgement symbolPrefixedVarName ref var

    return s!"{baseTex}\\left[{valTex}/{varTex}\\right]"
  | ref, .node _ catName #[
      base@(.node _ catName₀ _),
      .atom _ "^",
      var@(.node _ symbolPrefixedVarName _),
      .node _ `null level
    ] => do
    if catName != catName₀ then
      throwUnsupportedSyntax

    if !symbolPrefix.isPrefixOf catName then throwUnsupportedSyntax
    if !symbolPrefix.isPrefixOf symbolPrefixedVarName then throwUnsupportedSyntax

    let baseTex ← texElabSymbolOrJudgement catName ref base
    let varTex ← texElabSymbolOrJudgement symbolPrefixedVarName ref var

    if !(← getOptions).get lott.tex.locallyNameless.name lott.tex.locallyNameless.defValue then
      return baseTex

    if let some level := level[1]? then
      let levelTex ← texElabIdx level
      return s!"\{{baseTex}}^\{{varTex}#{levelTex}}"
    else
      return s!"\{{baseTex}}^\{{varTex}}"
  | ref, .node _ catName #[
      base@(.node _ catName₀ _),
      .atom _ "^^",
      val@(.node _ symbolPrefixedValName _),
      .node _ `null level,
      altRef@(.node _ `null locallyNamelessSubstAlternative)
    ] => do
    if catName != catName₀ then
      throwUnsupportedSyntax

    if !symbolPrefix.isPrefixOf catName then throwUnsupportedSyntax
    if !symbolPrefix.isPrefixOf symbolPrefixedValName then throwUnsupportedSyntax

    let baseTex ← texElabSymbolOrJudgement catName ref base
    let valTex ← texElabSymbolOrJudgement symbolPrefixedValName ref val

    if !(← getOptions).get lott.tex.locallyNameless.name lott.tex.locallyNameless.defValue then
      let varTex ← match locallyNamelessSubstAlternative with
        |  #[.atom _ "/", var@(.node _ symbolPrefixedVarName _)] =>
          if !symbolPrefix.isPrefixOf symbolPrefixedVarName then
            throwUnsupportedSyntax

          texElabSymbolOrJudgement symbolPrefixedVarName ref var
        | #[] =>
          logErrorAt altRef
            "variable name must be provided with '/x' for alternative tex substitution rendering when lott.tex.locallyNameless is set to false"
          throwUnsupportedSyntax
        | _ => throwUnsupportedSyntax
      return s!"{baseTex}\\left[{valTex}/{varTex}\\right]"

    if let some level := level[1]? then
      let levelTex ← texElabIdx level
      return s!"\{{baseTex}}^\{{valTex}#{levelTex}}"
    else
      return s!"\{{baseTex}}^\{{valTex}}"
  | ref, .node _ catName #[
      .atom _ "\\",
      var@(.node _ symbolPrefixedVarName _),
      .node _ `null level,
      .atom _ "^",
      base@(.node _ catName₀ _)
    ] => do
    if catName != catName₀ then
      throwUnsupportedSyntax

    if !symbolPrefix.isPrefixOf catName then throwUnsupportedSyntax
    if !symbolPrefix.isPrefixOf symbolPrefixedVarName then throwUnsupportedSyntax

    let baseTex ← texElabSymbolOrJudgement catName ref base
    let varTex ← texElabSymbolOrJudgement symbolPrefixedVarName ref var

    if !(← getOptions).get lott.tex.locallyNameless.name lott.tex.locallyNameless.defValue then
      return s!"\{{baseTex}}"

    if let some level := level[1]? then
      let levelTex ← texElabIdx level
      return s!"\\leftidx\{{varTex}#{levelTex}}\{{baseTex}}\{}"
    else
      return s!"\\leftidx\{{varTex}}\{{baseTex}}\{}"
  | ref, .node _ parentCatName #[stx@(.node _ childCatName _)] => do
    let some parentQualified := parentCatName.erasePrefix? symbolPrefix | throwUnsupportedSyntax
    let some childQualified := childCatName.erasePrefix? symbolPrefix | throwUnsupportedSyntax
    let some { parent, .. } := childExt.getState (← getEnv) |>.find? childQualified | throwUnsupportedSyntax
    if parent != parentQualified then throwUnsupportedSyntax

    texElabSymbolOrJudgement childCatName ref stx
  | _, _ => throwUnsupportedSyntax

def texElabSymbolOrJudgement (catName : Name) (ref stx : Syntax) : TermElabM String := do
  let env ← getEnv
  let texPrePost? := do
    let qualified ← catName.erasePrefix? symbolPrefix
    let { texPrePost?, .. } ← symbolExt.getState env |>.find? qualified
    texPrePost?

  let rawTex ← match lottTexElabAttribute.getEntries (← getEnv) catName with
    | [] =>
      try
        (try texElabMetavar ref stx catch _ => texElabVariable ref stx)
      catch _ =>
        throwErrorAt ref
          "tex elaboration function for '{catName}' has not been implemented{indentD stx}"
    | elabFns =>
      try texElabWithFns elabFns catch ex =>
        (try texElabMetavar ref stx catch _ =>
          (try texElabVariable ref stx catch _ => throw ex))

  if let some (texPre, texPost) := texPrePost? then
    return s!"{texPre} {rawTex} {texPost}"
  else
    return rawTex
where
  texElabWithFns
    | [] => unreachable!
    | [elabFn] => elabFn.value ref stx
    | elabFn :: elabFns => do
      try
        elabFn.value ref stx
      catch ex => match ex with
        | .internal id _ =>
          if id == unsupportedSyntaxExceptionId then texElabWithFns elabFns else throw ex
        | _ => throw ex

end

private
def resolveSymbol (symbolName : Ident) (allowSuffix := true) : CommandElabM Name := do
  let name := symbolName.getId
  let state := aliasExt.getState (← getEnv)

  let find (n : Name) := if allowSuffix then
      state.byAlias.matchPrefix n.toString 0
    else
      state.byAlias.find? n.toString

  -- First check if the name itself is present in the state.
  match find name with
    -- If not, check if it's present when prepending the current namespace.
  | none => match find <| (← getCurrNamespace) ++ name with
    -- Otherwise, check the namespaces we've opened.
    | none =>
      let names ← resolveOpensNames name state #[] <| ← getOpenDecls
      let aliases := names.filterMap find
      match aliases.foldl (fun acc a => acc.insert a.canon a) (mkNameMap _) |>.toList with
      | [] => throwErrorAt symbolName "unknown lott symbol {symbolName}"
      | [(canon, _)] => pure canon
      | results =>
        let results := results.toArray.map Prod.snd
        let sortedResults := results.qsort (·.alias.toString.length < ·.alias.toString.length)
        match sortedResults.filter (·.alias.toString.length == sortedResults[0]!.alias.toString.length) with
        | #[] => unreachable!
        | #[{ canon, .. }] => pure canon
        | results => throwErrorAt symbolName
            "ambiguous lott symbol {symbolName}; found multiple matches: {results.map (·.alias)}"
    | some { canon, .. } => pure canon
  | some { canon, .. } => pure canon
where
  resolveOpensNames name state acc
    | [] => pure acc
    | .simple ns except :: decls => do
      let mut acc := acc
      if !except.contains name then
        acc := acc.push <| ns ++ name
      resolveOpensNames name state acc decls
    | .explicit id declName :: decls => do
      let mut acc := acc
      if id = name then
        acc := acc.push declName
      resolveOpensNames name state acc decls

private
def judgementPrefix := `Lott.Judgement

partial
def _root_.Lott.IR.ofStx (stx : TSyntax `stx) (l? : Option Ident := none) : CommandElabM IR := do
  let l := l?.getD <| ← mkFreshIdent stx
  match stx with
  | `(stx| $name:ident) => do
    let name' := mkIdentFrom name <| name.getId.getFinal
    return mk name' <| .category (← resolveSymbol name)
  | `(stx| $s:str) => return mk l <| .atom s.getString
  | `(stx| sepBy($[$ps]*, $sep)) =>
    return mk l <| .sepBy (← ps.mapM ofStx) sep.getString
  | `(stx| optional($[$ps]*)) =>
    return mk l <| .optional <| ← ps.mapM ofStx
  | _ => throwUnsupportedSyntax

partial
def _root_.Lott.IR.ofProdArg (arg : TSyntax ``Lott.prodArg) : CommandElabM IR := do
  let `(prodArg| $[$l?:ident:]?$stx:stx) := arg | throwUnsupportedSyntax
  ofStx stx l?

private partial
def _root_.Lott.IR.toExprArgs (ir : Array IR) (ids binders : Array Name)
  : CommandElabM (TSepArray `term ",") :=
  ir.filterMapM (β := Term) fun | ir@(mk l _) => do
      if (← IR.toType ids binders ir).isNone then
        return none

      return some l

def Syntax.mkSymbolEmbed (stx : Syntax) : Term :=
  .mk <| mkNode ``Lott.symbolEmbed #[mkAtom "[[", stx, mkAtom "]]"]

def _root_.Lean.Syntax.mkTypeAscription (stx type : Syntax) : Term :=
  .mk <| mkNode ``Lean.Parser.Term.typeAscription
    #[mkAtom "(", stx, mkAtom ":", mkNullNode #[type], mkAtom ")"]

def _root_.Lean.Syntax.mkMap (collection pat body : Term) (mapName : Name) : MacroM Term :=
  `($(collection).$(mkIdent mapName):ident fun $pat => $body)

private partial
def _root_.Lott.IR.toMacroSeqItems (ir : Array IR) (canon : Name) (ids binders : Array Name)
  : CommandElabM (TSyntaxArray ``Lean.Parser.Term.doSeqItem) :=
  ir.filterMapM fun
    | mk l (.category _) => do
      if binders.contains l.getId then
        return none

      `(doSeqItem| let $l := Lott.Syntax.mkSymbolEmbed $l)
    | mk _ (.atom _) => return none
    | mk l (.sepBy ir sep) => do
      let catName := sepByPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toMacroSeqItems ir canon ids binders
      let exprArgs ← IR.toExprArgs ir ids binders
      let go ← mkFreshIdent l

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx =>
            let rec $go:ident : Lean.Syntax → Lean.MacroM (Bool × Lean.Syntax.Term)
              | Lean.Syntax.node _ $(quote catName) #[
                  Lean.Syntax.atom _ "</",
                  symbol,
                  Lean.Syntax.atom _ "//",
                  pat,
                  Lean.Syntax.atom _ "in",
                  collection,
                  Lean.Syntax.atom _ "/>"
                ] => do
                let (singleton, symbol) ← $go:ident symbol
                let mapName := if singleton then `map else `flatMap
                return (false, ← Lean.Syntax.mkMap (.mk collection) (.mk pat) (.mk symbol) mapName)
              | Lean.Syntax.node _ $(quote catName) #[
                  lhs@(Lean.Syntax.node _ $(quote catName) _),
                  Lean.Syntax.atom _ $(quote sep.trim),
                  rhs@(Lean.Syntax.node _ $(quote catName) _)
                ] => do
                let (lhsSingleton, lhs) ← $go:ident lhs
                let (rhsSingleton, rhs) ← $go:ident rhs
                let combineName := if lhsSingleton then ``List.cons else ``HAppend.hAppend
                let rhs := if rhsSingleton then
                    Lean.Syntax.mkCApp ``List.cons #[rhs, Lean.mkIdent ``List.nil]
                  else
                    rhs
                return (false, Lean.Syntax.mkCApp combineName #[lhs, rhs])
              | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
                $seqItems*
                return (true, ← Lott.IR.foldrProd #[$exprArgs,*])
              | _ => Lean.Macro.throwUnsupported
            let (singleton, x) ← $go:ident stx
            if singleton then
              pure <| Lean.Syntax.mkCApp ``List.cons #[x, Lean.mkIdent ``List.nil]
            else
              pure x
          | none => pure <| mkIdent ``List.nil)
    | mk l (.optional ir) => do
      let catName := optionalPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toMacroSeqItems ir canon ids binders
      let exprArgs ← IR.toExprArgs ir ids binders
      let go ← mkFreshIdent l

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx =>
            let rec $go:ident : Lean.Syntax → Lean.MacroM (Bool × Lean.Syntax.Term)
              | Lean.Syntax.node _ $(quote catName) #[
                  Lean.Syntax.atom _ "</",
                  symbol,
                  Lean.Syntax.atom _ "//",
                  cond,
                  Lean.Syntax.atom _ "/>"
                ] => do
                let (option, symbol) ← $go:ident symbol
                let modifierName := if option then ``Option.keepIf else ``Option.someIf
                return (
                  true,
                  Lean.Syntax.mkCApp modifierName #[symbol, .mk cond]
                )
              | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
                $seqItems*
                return (false, ← Lott.IR.foldrProd #[$exprArgs,*])
              | _ => Lean.Macro.throwUnsupported
            let (option, x) ← $go:ident stx
            if option then
              pure x
            else
              pure <| Lean.Syntax.mkCApp ``Option.some #[x]
          | none => pure <| mkIdent ``Option.none)

private partial
def _root_.Lott.IR.toTexSeqItems (ir : Array IR) (canon : Name)
  : CommandElabM (TSyntaxArray ``Lean.Parser.Term.doSeqItem) :=
  return Prod.fst <| ← ir.foldrM (init := (#[], false)) fun
    | mk l (.category n), (items, lastWasNonAtom) => do
      let space := if lastWasNonAtom then " \\;" else ""
      let item ← `(doSeqItem| let $l ← (· ++ $(quote space)) <$> Lott.texElabSymbolOrJudgement $(quote <| symbolPrefix ++ n) ref $l)
      return (items.push item, true)
    | mk l (.atom s), (items, _) =>
      return (items.push <| ← `(doSeqItem| let $l := $(quote <| atomToTex s)), false)
    | mk l (.sepBy ir sep), (items, lastWasNonAtom) => do
      let catName := sepByPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir canon
      let joinArgs := IR.toJoinArgs ir
      let go ← mkFreshIdent l

      let space := if lastWasNonAtom then " \\;" else ""

      let item ← `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx =>
            let rec $go:ident : Lean.Syntax → Lean.Elab.Term.TermElabM String
              | Lean.Syntax.node _ $(quote catName) #[
                  Lean.Syntax.atom _ "</",
                  symbol,
                  Lean.Syntax.atom _ "//",
                  pat,
                  Lean.Syntax.atom _ "in",
                  collection,
                  Lean.Syntax.atom _ "/>"
                ] => do
                let symbolTex ← $go:ident symbol
                -- TODO: Optionally include pat and collection here.
                return s!"\\overline\{{symbolTex}}"
              | Lean.Syntax.node _ $(quote catName) #[
                  lhs@(Lean.Syntax.node _ $(quote catName) _),
                  Lean.Syntax.atom _ $(quote sep.trim),
                  rhs@(Lean.Syntax.node _ $(quote catName) _)
                ] => do
                let lhsTex ← $go:ident lhs
                let rhsTex ← $go:ident rhs
                return s!"{lhsTex} {$(quote <| atomToTex sep)} {rhsTex}"
              | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
                $seqItems*
                return " ".intercalate [$joinArgs,*]
              | _ => Lean.Elab.throwUnsupportedSyntax
            let tex ← $go:ident stx
            pure <| tex ++ $(quote space)
          | none => pure "")
      return (items.push item, true)
    | mk l (.optional ir), (items, lastWasNonAtom) => do
      let catName := optionalPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir canon
      let joinArgs := IR.toJoinArgs ir
      let go ← mkFreshIdent l

      let space := if lastWasNonAtom then " \\;" else ""
      let item ← `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx =>
            let rec $go:ident : Lean.Syntax → Lean.Elab.Term.TermElabM String
              | Lean.Syntax.node _ $(quote catName) #[
                  Lean.Syntax.atom _ "</",
                  symbol,
                  Lean.Syntax.atom _ "//",
                  cond,
                  Lean.Syntax.atom _ "/>"
                ] => do
                let symbolTex ← $go:ident symbol
                -- TODO: Optionally include cond here.
                return s!"\\overline\{{symbolTex}}"
              | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
                $seqItems*
                return " ".intercalate [$joinArgs,*]
              | _ => Lean.Elab.throwUnsupportedSyntax
            let tex ← $go:ident stx
            pure <| tex ++ $(quote space)
          | none => pure "")
      return (items.push item, true)
where
  atomToTex (atom : String) :=
    let leadingWs := atom.data[0]?.map Char.isWhitespace |>.getD false
    let trailingWs := atom.data.getLast?.map Char.isWhitespace |>.getD false
    let tex := if atom.trim.data.all (fun c => c.isAlpha || c.isSubscriptAlpha) then
        s!"\\lottkw\{{atom.trim.texEscape}}"
      else
        s!"\\lottsym\{{atom.trim.texEscape}}"
    (if leadingWs then "\\; " else "") ++ tex ++ (if trailingWs then " \\;" else "")

private partial
def _root_.Lott.IR.toIsChildCtor (prodIdent isIdent : Ident) (qualified pqualified : Name) (ir pir : Array IR)
  (binders : Array Name) : CommandElabM (TSyntax ``Lean.Parser.Command.ctor) := do
  if ir.size != pir.size then
    throwErrorAt prodIdent "length of child production ({ir.size}) doesn't match length of parent production ({pir.size})"

  let (ctorTypeRetArgs, ctorTypeArgs) ← go (ir.zip pir)
  let binders ← ctorTypeRetArgs.filterMapM fun
    | `(Lean.binderIdent| $_:hole) => return none
    | `(Lean.binderIdent| $i:ident) => `(bracketedBinder| {$i})
    | _ => throwUnsupportedSyntax
  let ctorType ← foldrArrow ctorTypeArgs <| ← ``($isIdent ($(mkIdent <| pqualified ++ prodIdent.getId) $(← toTerms ctorTypeRetArgs)*))
  return ← `(ctor| | $prodIdent:ident $binders:bracketedBinder* : $ctorType)
where
  go (irs : Array (IR × IR)) (patAcc : TSyntaxArray ``Lean.binderIdent := #[])
    (propAcc : Array Term := #[])
    : CommandElabM (TSyntaxArray ``Lean.binderIdent × Array Term) := do
    let some (mk l' ir, mk l pir) := irs[0]? | return (patAcc, propAcc)
    let irs' := irs.extract 1 irs.size

    if binders.contains l'.getId then
        return ← go irs' patAcc propAcc

    let lbi ← `(Lean.binderIdent| $l:ident)
    let l'bi ← `(Lean.binderIdent| $l':ident)
    let hole ← `(Lean.binderIdent| _)

    match ir, pir with
    | .category n, .category np => do
      if n == np then
        return ← go irs' (patAcc.push hole) propAcc

      if some np == ((childExt.getState (← getEnv)).find? n).map (·.parent) then
        let .str _ nStr := n | throwUnsupportedSyntax
        let isName := np ++ Name.str .anonymous nStr |>.appendBefore "Is"
        return ← go irs' (patAcc.push lbi) <| propAcc.push <| ← `($(mkIdent isName) $l)

      throwErrorAt prodIdent "couldn't find parent/child relationship between {pqualified} and {qualified}"
    | .atom s, .atom sp => do
      if s != sp then
        throwErrorAt prodIdent "mismatched atoms \"{s}\" and \"{sp}\""

      go irs' patAcc propAcc
    | .sepBy ir sep, .sepBy pir psep => do
      if sep != psep then
        throwErrorAt prodIdent "mismatched separators \"{sep}\" and \"{psep}\""

      if ir.size != pir.size then
        throwErrorAt prodIdent "length of child sepBy ({ir.size}) doesn't match length of parent sepBy ({pir.size})"

      match ← go (ir.zip pir) with
      -- In this case, the sepBy doesn't actually contain anything stored in the datatype so we can
      -- just skip it.
      | (#[], #[]) => go irs' patAcc propAcc
      -- In this case, there is a list with stuff in it, but it doesn't contain anything for us to
      -- check, so we can just add an underscore pattern argument and proceed.
      | (_, #[]) => go irs' (patAcc.push hole) propAcc
      | (#[patArg], props) => go irs' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $patArg ∈ $l, $(← foldlAnd props))
      | (patArgs, props) =>
        let prod ← liftMacroM <| foldrProd <| ← toTerms patArgs
        go irs' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $l'bi ∈ $l, let $prod:term := $l'; $(← foldlAnd props))
    | .optional ir, .optional pir => do
      if ir.size != pir.size then
        throwErrorAt prodIdent "length of child optional ({ir.size}) doesn't match length of parent optional ({pir.size})"

      match ← go (ir.zip pir) with
      -- In this case, the optional doesn't actually contain anything stored in the datatype so we
      -- can just skip it.
      | (#[], #[]) => go irs' patAcc propAcc
      -- In this case, there is a list with stuff in it, but it doesn't contain anything for us to
      -- check, so we can just add an underscore pattern argument and proceed.
      | (_, #[]) => go irs' (patAcc.push hole) propAcc
      | (#[patArg], props) => go irs' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $patArg:binderIdent ∈ $l, $(← foldlAnd props))
      | (patArgs, props) =>
        let prod ← liftMacroM <| foldrProd <| ← toTerms patArgs
        go irs' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $l'bi ∈ $l, let $prod:term := $l'; $(← foldlAnd props))
    | _, _ => throwErrorAt prodIdent "mismatched syntax"

private
def freeName (varName : Name) (typeName : Name) : CommandElabM Name := do
  let ns ← getCurrNamespace
  let typeName := typeName.replacePrefix ns .anonymous
  match varName.replacePrefix ns .anonymous with
  | .str .anonymous s => return typeName ++ Name.appendAfter `free s |>.appendAfter "s"
  | n => return typeName ++ `free ++ n.appendAfter "s"

private partial
def toFreeMatchAlt (prodId : Ident) (ir : Array IR) (subst : Name × Name)
  (binders : Array Name) : CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let (patArgs, appendArgs) ← goMany ir
  let rhs ← foldlAppend appendArgs
  `(matchAltExpr| | $prodId $patArgs* => $rhs)
where
  goMany (ir : Array IR) : CommandElabM (Array Term × Array Term) := do
    let (patArg?s, appendArg?s) ← Array.unzip <$> ir.mapM go
    return (patArg?s.filterMap id, appendArg?s.filterMap id)
  go (ir : IR) : CommandElabM (Option Term × Option Term) := do
    let .mk l irt := ir

    if binders.contains l.getId then
      return (none, none)

    match irt with
    | .category n => do
      if n == subst.fst then
        return (l, some <| ← ``(match $l:ident with | .free x => [x] | .bound _ => []))
      if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
        if substitutions.contains subst then
          let freeId := mkIdent <| ← freeName subst.fst n
          return (l, some <| ← ``($freeId $l))
      return (← ``(_), none)
    | .atom _ => return (none, none)
    | .sepBy ir _ => match ← goMany ir with
      | (#[], _) => return (none, none)
      | (_, #[]) => return (← ``(_), none)
      | (patArgs, appendArgs) =>
        let prod ← liftMacroM <| foldrProd patArgs
        return (
          l,
          ← `((List.mapMem $l fun $prod _ => $(← foldlAppend appendArgs)).flatten)
        )
    | .optional ir => match ← goMany ir with
      | (#[], _) => return (none, none)
      | (_, #[]) => return (← ``(_), none)
      | (patArgs, appendArgs) =>
        let prod ← liftMacroM <| foldrProd patArgs
        return (
          l,
          ← `(
            (Option.mapMem $l fun $prod _ => $(← foldlAppend appendArgs)).getD []
          )
        )

private
def locallyClosedName (varName : Name) (typeName : Name) : CommandElabM Name := do
  let ns ← getCurrNamespace
  let typeName := typeName.replacePrefix ns .anonymous
  return typeName ++ varName.replacePrefix ns .anonymous |>.appendAfter "LocallyClosed"

private partial
def containsVar (varName : Name) (ir : Array IR) (ids binders : Array Name) : Bool :=
  ir.any fun
    | mk l (.category n) => n == varName && !(binders.contains l.getId || ids.contains l.getId)
    | mk _ (.atom _) => false
    | mk _ (.sepBy ir _)
    | mk _ (.optional ir) => containsVar varName ir ids binders

private partial
def toLocallyClosedCtors (prodId locallyClosedId idxId : Ident) (qualified : Name) (ir : Array IR)
  (subst : Name × Name) (ids binders : Array Name)
  : CommandElabM (Array (TSyntax ``Lean.Parser.Command.ctor)) := do
  if containsVar subst.fst ir ids binders then
    let #[mk _ (.category _)] := ir |
      throwErrorAt prodId "generation of locally closed definitions is not yet supported for complicated productions"
    let boundProdId := mkIdentFrom prodId <| prodId.getId.appendAfter "_bound"
    let freeProdId := mkIdentFrom prodId <| prodId.getId.appendAfter "_free"
    return #[
      ← `(ctor| | $boundProdId:ident {$idxId} {x} : x < $idxId → $locallyClosedId ($fullProdId (.bound x)) $idxId),
      ← `(ctor| | $freeProdId:ident {$idxId} : $locallyClosedId ($fullProdId (.free _)) $idxId)
    ]
  else
    let (ctorTypeRetArgs, ctorTypeArgs) ← go ir
    let binders ← ctorTypeRetArgs.filterMapM fun
      | `(Lean.binderIdent| $_:hole) => return none
      | `(Lean.binderIdent| $i:ident) => `(bracketedBinder| {$i})
      | _ => throwUnsupportedSyntax
    let ctorType ← foldrArrow ctorTypeArgs <| ←
      ``($locallyClosedId ($fullProdId $(← toTerms ctorTypeRetArgs)*) $idxId)
    return #[← `(ctor| | $prodId:ident {$idxId} $binders:bracketedBinder* : $ctorType)]
where
  fullProdId := mkIdent <| qualified ++ prodId.getId
  inc := ir.any fun
    | mk l (.category n) => n == subst.fst && binders.contains l.getId
    | _ => false
  go (irs : Array IR) (patAcc : TSyntaxArray ``Lean.binderIdent := #[]) (propAcc : Array Term := #[])
    : CommandElabM (TSyntaxArray ``Lean.binderIdent × Array Term) := do
    let some (mk l ir) := irs[0]? | return (patAcc, propAcc)
    let irs := irs.extract 1 irs.size

    if binders.contains l.getId then
      return ← go irs patAcc propAcc

    let lbi ← `(Lean.binderIdent| $l:ident)
    let hole ← `(Lean.binderIdent| _)

    match ir with
    | .category n => do
      if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
        if substitutions.contains subst then
          let locallyClosedId := mkIdent <| ← locallyClosedName subst.fst n
          let prop ← if inc then
              ``($locallyClosedId $l ($idxId + 1))
            else
              ``($locallyClosedId $l $idxId)
          go irs (patAcc.push lbi) <| propAcc.push prop
        else
          go irs (patAcc.push hole) propAcc
      else
        go irs (patAcc.push hole) propAcc
    | .atom _ => go irs patAcc propAcc
    | .sepBy ir _
    | .optional ir => do
      match ← go ir with
      -- In this case, the sepBy or optional doesn't actually contain anything stored in the
      -- datatype so we can just skip it.
      | (#[], #[]) => go irs patAcc propAcc
      -- In this case, there is stuff in it, but it doesn't contain anything for us to check, so we
      -- can just add an underscore pattern argument and proceed.
      | (_, #[]) => go irs (patAcc.push hole) propAcc
      | (#[patArg], props) => go irs (patAcc.push lbi) <| propAcc.push <| ←
          `(∀ $patArg:binderIdent ∈ $l, $(← foldlAnd props))
      | (patArgs, props) =>
        let propAcc' ← props.mapM fun prop =>
          do `(∀ x ∈ $l, let $(← liftMacroM <| foldrProd <| ← toTerms patArgs):term := x; $prop)
        go irs (patAcc.push lbi) <| propAcc ++ propAcc'

private
def substName (varName : Name) : CommandElabM Name :=
  return varName.replacePrefix (← getCurrNamespace) .anonymous |>.appendAfter "_subst"

private partial
def toSubstPatternAndArgs (ir : Array IR) (varType valType : Name) (varId valId :  Ident)
  (bindOf? binderId? : Option Ident) : CommandElabM (Option (Array Term × Array Term)) := do
  let patsAndArgsAndFounds ← ir.filterMapM fun (mk l irt) => do
    if some l == bindOf? then return none

    match irt with
    | .category n =>
      if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
        if substitutions.contains (varType, valType) then
          let substId := mkIdent <| n ++ (← substName varType)
          return some (l, ← `($substId:ident $l $varId $valId), true)

      return some (l, l, false)
    | .atom _ => return none
    | .sepBy ir _ =>
      let some (pattern, args) ←
        toSubstPatternAndArgs ir varType valType varId valId bindOf? binderId? |
        return some (l, (l : Term), false)
      let patProd ← liftMacroM <| foldrProd pattern
      let argsProd ← liftMacroM <| foldrProd args
      return some (l, ← `(List.mapMem $l fun $patProd _ => $argsProd), true)
    | .optional ir =>
      let some (pattern, args) ←
        toSubstPatternAndArgs ir varType valType varId valId bindOf? binderId? |
        return some (l, (l : Term), false)
      let patProd ← liftMacroM <| foldrProd pattern
      let argsProd ← liftMacroM <| foldrProd args
      let arg ← `(Option.mapMem $l fun $patProd _ => $argsProd)
      return some (l, arg, true)
  let (pats, argsAndFounds) := patsAndArgsAndFounds.unzip
  let (args, founds) := argsAndFounds.unzip
  if founds.any id then
    return some (pats, args)
  else
    return none

private
def openName (varName : Name) : CommandElabM Name :=
  return varName.replacePrefix (← getCurrNamespace) .anonymous |>.appendAfter "_open"

private partial
def toVarOpenPatternAndArgs (ir : Array IR) (varType valType : Name) (varId idxId :  Ident)
  (bindOf? binderId? : Option Ident) : CommandElabM (Option (Array Term × Array Term)) := do
  let patsAndArgsAndFounds ← ir.filterMapM fun (mk l irt) => do
    if some l == bindOf? then return none

    match irt with
    | .category n =>
      if some l != binderId? && n == varType then
        return some (l, ← `(if .bound $idxId = $l then .free $varId else $l), true)

      if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
        if substitutions.contains (varType, valType) then
          return some (l, ← `($(mkIdent <| n ++ (← openName varType)):ident $l $varId $idxId), true)

      return some (l, l, false)
    | .atom _ => return none
    | .sepBy ir _ =>
      let some (pattern, args) ←
        toVarOpenPatternAndArgs ir varType valType varId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let patProd ← liftMacroM <| foldrProd pattern
      let argsProd ← liftMacroM <| foldrProd args
      return some (l, ← `(List.mapMem $l fun $patProd _ => $argsProd), true)
    | .optional ir =>
      let some (pattern, args) ←
        toVarOpenPatternAndArgs ir varType valType varId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let patProd ← liftMacroM <| foldrProd pattern
      let argsProd ← liftMacroM <| foldrProd args
      let arg ← `(Option.mapMem $l fun $patProd _ => $argsProd)
      return some (l, arg, true)
  let (pats, argsAndFounds) := patsAndArgsAndFounds.unzip
  let (args, founds) := argsAndFounds.unzip
  if founds.any id then
    return some (pats, args)
  else
    return none

private partial
def toValOpenPatternAndArgs (ir : Array IR) (varType valType : Name) (valId idxId :  Ident)
  (bindOf? binderId? : Option Ident) : CommandElabM (Option (Array Term × Array Term)) := do
  let patsAndArgsAndFounds ← ir.filterMapM fun (mk l irt) => do
    if some l == bindOf? then return none

    match irt with
    | .category n =>
      if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
        if substitutions.contains (varType, valType) then
          return some (l, ← `($(mkIdent <| n ++ (← openName valType)):ident $l $valId $idxId), true)

      return some (l, l, false)
    | .atom _ => return none
    | .sepBy ir _ =>
      let some (pattern, args) ←
        toValOpenPatternAndArgs ir varType valType valId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let patProd ← liftMacroM <| foldrProd pattern
      let argsProd ← liftMacroM <| foldrProd args
      return some (l, ← `(List.mapMem $l fun $patProd _ => $argsProd), true)
    | .optional ir =>
      let some (pattern, args) ←
        toValOpenPatternAndArgs ir varType valType valId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let patProd ← liftMacroM <| foldrProd pattern
      let argsProd ← liftMacroM <| foldrProd args
      let arg ← `(Option.mapMem $l fun $patProd _ => $argsProd)
      return some (l, arg, true)
  let (pats, argsAndFounds) := patsAndArgsAndFounds.unzip
  let (args, founds) := argsAndFounds.unzip
  if founds.any id then
    return some (pats, args)
  else
    return none

private
def closeName (varName : Name) : CommandElabM Name :=
  return varName.replacePrefix (← getCurrNamespace) .anonymous |>.appendAfter "_close"

private partial
def toClosePatternAndArgs (ir : Array IR) (varType valType : Name) (varId idxId :  Ident)
  (bindOf? binderId? : Option Ident) : CommandElabM (Option (Array Term × Array Term)) := do
  let patsAndArgsAndFounds ← ir.filterMapM fun (mk l irt) => do
    if some l == bindOf? then return none

    match irt with
    | .category n =>
      if some l != binderId? && n == varType then
        return some (l, ← `(if .free $varId = $l then .bound $idxId else $l), true)

      if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
        if substitutions.contains (varType, valType) then
          return some (l, ← `($(mkIdent <| n ++ (← closeName varType)):ident $l $varId $idxId), true)

      return some (l, l, false)
    | .atom _ => return none
    | .sepBy ir _ =>
      let some (pattern, args) ←
        toClosePatternAndArgs ir varType valType varId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let patProd ← liftMacroM <| foldrProd pattern
      let argsProd ← liftMacroM <| foldrProd args
      return some (l, ← `(List.mapMem $l fun $patProd _ => $argsProd), true)
    | .optional ir =>
      let some (pattern, args) ←
        toClosePatternAndArgs ir varType valType varId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let patProd ← liftMacroM <| foldrProd pattern
      let argsProd ← liftMacroM <| foldrProd args
      let arg ← `(Option.mapMem $l fun $patProd _ => $argsProd)
      return some (l, arg, true)
  let (pats, argsAndFounds) := patsAndArgsAndFounds.unzip
  let (args, founds) := argsAndFounds.unzip
  if founds.any id then
    return some (pats, args)
  else
    return none

def symbolEmbedIdent := mkIdent ``Lott.symbolEmbed

/- Metavariable syntax. -/

@[macro Lott.symbolEmbed]
private
def metavarImpl : Macro := fun
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ _ #[ident@(.ident ..)],
      .atom _ "]]"
    ] => return ident
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ _ #[«fun», .atom _ "@", idx],
      .atom _ "]]"
    ] => `(([[$(.mk «fun»):Lott.Symbol]] : _ → _) $(.mk idx):term)
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ _ #[.ident .., .atom _ "$", num@(.node _ `num _)],
      .atom _ "]]"
    ] => `(.bound $(.mk num))
  | _ => Macro.throwUnsupported

elab_rules : command | `($[locally_nameless%$ln]? metavar $names,*) => do
  let names := names.getElems.toList
  let canon :: aliases := names | throwUnsupportedSyntax
  let ns ← getCurrNamespace
  let canonQualified := ns ++ canon.getId
  let locallyNameless := ln.isSome

  -- Declare type and aliases.
  -- TODO: Is there any way we can make the ids have an opaque type which reveals nothing other than
  -- that they have a decidable equality relation?
  if locallyNameless then
    let idIdent := mkIdentFrom canon <| canon.getId.appendAfter "Id"
    elabCommand <| ← `(def $idIdent := Nat)
    elabCommand <| ← `(instance (x y : $idIdent) : Decidable (x = y) := Nat.decEq x y)
    elabCommand <| ←
      `(inductive $canon where
          | $(mkIdent `free):ident (id : $idIdent)
          | $(mkIdent `bound):ident (idx : Nat))
    elabCommand <| ← `(instance : SizeOf $canon := instSizeOfDefault $canon)
    elabCommand <| ←
      `(instance (x y : $canon) : Decidable (x = y) := match x, y with
          | .free idx, .free idy => if h : idx = idy then
              isTrue <| $(mkIdent <| canon.getId ++ `free.injEq) idx idy |>.mpr h
            else
              isFalse (h <| $(mkIdent <| canon.getId ++ `free.inj) ·)
          | .bound idxx, .bound idxy => if h : idxx = idxy then
              isTrue <| $(mkIdent <| canon.getId ++ `bound.injEq) idxx idxy |>.mpr h
            else
              isFalse (h <| $(mkIdent <| canon.getId ++ `bound.inj) ·)
          | .free _, .bound _
          | .bound _, .free _ => isFalse nofun)
    elabCommand <| ← `(instance : Coe $idIdent $canon where coe := .free)
  else
    elabCommand <| ← `(def $canon := Nat)
    elabCommand <| ← `(instance (x y : $canon) : Decidable (x = y) := Nat.decEq x y)

  -- Update environment extensions.
  for name in names do
    setEnv <| aliasExt.addEntry (← getEnv) { canon := canonQualified, alias := ns ++ name.getId }
  setEnv <| metaVarExt.addEntry (← getEnv) (canonQualified, locallyNameless)

  -- Declare syntax category. For metavariables we just declare the alias name parsers directly in
  -- the syntax category. This differs from variable parsers for non-terminals, for which we declare
  -- a separate variable category, then add a category parser for the variable category to the main
  -- non-terminal symbol category.
  let catName := symbolPrefix ++ canonQualified
  let parserAttrName := catName.appendAfter "_parser"
  setEnv <| ← Parser.registerParserCategory (← getEnv) parserAttrName catName .symbol

  -- Declare parsers in category.
  for alias in aliases do
    let aliasName@(.str .anonymous nameStr) := alias.getId | throwUnsupportedSyntax
    let parserIdent := mkIdentFrom alias <| canon.getId ++ aliasName.appendAfter "_parser"
    elabCommand <| ←
      `(@[Lott.Symbol_parser, $(mkIdent parserAttrName):ident]
        private
        def $parserIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <| Lott.identPrefix $(quote nameStr))

    if locallyNameless then
      let parserIdent := mkIdentFrom alias <| canon.getId ++ aliasName.appendAfter "_bound_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $(mkIdent parserAttrName):ident]
          private
          def $parserIdent : Parser :=
            leadingNode $(quote catName) Parser.maxPrec <|
              Lott.identPrefix $(quote nameStr) >> "$" >> num)

  let parserIdent := mkIdentFrom canon <| canon.getId.appendAfter "_idx_parser"
  elabCommand <| ←
    `(@[Lott.Symbol_parser, $(mkIdent parserAttrName):ident]
      private
      def $parserIdent : TrailingParser :=
        trailingNode $(quote catName) Parser.maxPrec 0 <|
          checkNoWsBefore >> "@" >> checkLineEq >> (Parser.ident <|> Parser.numLit))

/- Non-terminal syntax. -/

@[macro symbolEmbed]
private
def nonTerminalImpl : Macro := fun
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ _ #[.node _ _ #[ident@(.ident ..)] ],
      .atom _ "]]"
    ] => return ident
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node info kind #[.node _ _ #[«fun», .atom _ "@", idx] ],
      .atom _ "]]"
    ] => `(($(Syntax.mkSymbolEmbed (.node info kind #[«fun»])) : _ → _) $(.mk idx))
  -- NOTE: Could maybe make these even more resistant to false positives on user definitions by
  -- adding special intermediate nodes; not really any need though unless people actually run into
  -- problems.
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ catName #[
        base@(.node _ catName₀ _),
        .atom _ "[",
        val@(.node _ symbolPrefixedValName _),
        .atom _ "/",
        var@(.node _ symbolPrefixedVarName _),
        .atom _ "]"
      ],
      .atom _ "]]"
    ] => do
    if catName != catName₀ then
      Macro.throwUnsupported

    let some canonQualified := catName.erasePrefix? symbolPrefix | Macro.throwUnsupported
    if !symbolPrefix.isPrefixOf symbolPrefixedValName then Macro.throwUnsupported
    let some varName := symbolPrefixedVarName.erasePrefix? symbolPrefix | Macro.throwUnsupported

    let (_, varName) := canonQualified.removeCommonPrefixes varName
    let substName := canonQualified ++ varName.appendAfter "_subst"

    return .mkCApp substName #[
      Syntax.mkSymbolEmbed base,
      Syntax.mkSymbolEmbed var,
      Syntax.mkSymbolEmbed val
    ]
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ catName #[
        base@(.node _ catName₀ _),
        .atom _ "^",
        var@(.node _ symbolPrefixedVarName _),
        .node _ `null level
      ],
      .atom _ "]]"
    ] => do
    if catName != catName₀ then
      Macro.throwUnsupported

    let some canonQualified := catName.erasePrefix? symbolPrefix | Macro.throwUnsupported
    let some varName := symbolPrefixedVarName.erasePrefix? symbolPrefix | Macro.throwUnsupported

    let (_, varName) := canonQualified.removeCommonPrefixes varName
    let openName := canonQualified ++ varName.appendAfter "_open"

    return .mkCApp openName <| #[
      Syntax.mkSymbolEmbed base,
      Syntax.mkSymbolEmbed var
    ] ++ (level[1]?.map TSyntax.mk).toArray
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ catName #[
        base@(.node _ catName₀ _),
        .atom _ "^^",
        val@(.node _ symbolPrefixedValName _),
        .node _ `null level,
        .node _ `null _
      ],
      .atom _ "]]"
    ] => do
    if catName != catName₀ then
      Macro.throwUnsupported

    let some canonQualified := catName.erasePrefix? symbolPrefix | Macro.throwUnsupported
    let some valName := symbolPrefixedValName.erasePrefix? symbolPrefix | Macro.throwUnsupported

    let (_, valName) := canonQualified.removeCommonPrefixes valName
    let openName := canonQualified ++ valName.appendAfter "_open"

    return .mkCApp openName <| #[
      Syntax.mkSymbolEmbed base,
      Syntax.mkSymbolEmbed val
    ] ++ (level[1]?.map TSyntax.mk).toArray
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ catName #[
        .atom _ "\\",
        var@(.node _ symbolPrefixedVarName _),
        .node _ `null level,
        .atom _ "^",
        base@(.node _ catName₀ _)
      ],
      .atom _ "]]"
    ] => do
    if catName != catName₀ then
      Macro.throwUnsupported

    let some canonQualified := catName.erasePrefix? symbolPrefix | Macro.throwUnsupported
    let some varName := symbolPrefixedVarName.erasePrefix? symbolPrefix | Macro.throwUnsupported

    let (_, varName) := canonQualified.removeCommonPrefixes varName
    let openName := canonQualified ++ varName.appendAfter "_close"

    return .mkCApp openName <| #[
      Syntax.mkSymbolEmbed base,
      Syntax.mkSymbolEmbed var
    ] ++ (level[1]?.map TSyntax.mk).toArray
  | _ => Macro.throwUnsupported

private
structure BindConfig where
  of : Ident
  in' : Array Ident
deriving BEq

private
def BindConfig.find? (bc : BindConfig) (n : Name) : Option Ident := Id.run do
  if bc.of.getId == n then
    return bc.of

  bc.in'.find? (·.getId == n)

instance : ToStream BindConfig (Array Ident) where
  toStream | { of, in' } => in'.push of

private
structure Production where
  name : Ident
  ir : Array IR
  expand? : Option Term
  bindConfig? : Option BindConfig
  ids : Array Name
  «notex» : Bool
  tex? : Option Term

private
def Production.binders (prod : Production) : Array Name :=
  prod.bindConfig?.toArray.map fun { of, .. } => of.getId

private
structure NonTerminal where
  canon : Ident
  aliases : Array Ident
  prods : Array Production
  parent? : Option Ident
  substitutions? : Option (Array (Name × Name))
  texPrePost? : Option (String × String)

namespace NonTerminal

private
def qualified (nt : NonTerminal) : CommandElabM Name :=
  return (← getCurrNamespace) ++ nt.canon.getId

private
def catName (nt : NonTerminal) : CommandElabM Name :=
  return symbolPrefix ++ (← nt.qualified)

private
def varCatName (nt : NonTerminal) : CommandElabM Name :=
  return variablePrefix ++ (← nt.qualified)

private
def parserAttrName (nt : NonTerminal) : CommandElabM Name :=
  return (← nt.catName).appendAfter "_parser"

private
def varParserAttrName (nt : NonTerminal) : CommandElabM Name :=
  return (← nt.varCatName).appendAfter "_parser"

end NonTerminal

private partial
def NonTerminal.shallowClosure (nt : NonTerminal) (qualifiedLocalMap : NameMap NonTerminal)
  : CommandElabM NameSet := do
  let mut res := .empty |>.insert (← nt.qualified)
  let mut queue := #[nt]
  repeat do
    let some nt := queue.back? | break
    queue := queue.pop

    for { ir, .. } in nt.prods do
      for name in irsClosure ir do
        if res.contains name then
          continue

        res := res.insert name

        let some nt := qualifiedLocalMap.find? name | continue
        queue := queue.push nt
  return res
where
  irClosure : IR → NameSet
    | .mk _ (.category n) => .empty |>.insert n
    | .mk _ (.atom _) => .empty
    | .mk _ (.sepBy ir _)
    | .mk _ (.optional ir) => irsClosure ir
  irsClosure ir := ir.foldl (·.union <| irClosure ·) .empty

private
def elabMutualCommands (cs : Array Command) : CommandElabM Unit :=
  match cs with
  | #[] => pure ()
  | #[c] => elabCommand c
  | cs => do elabCommand <| ← `(mutual $cs* end)

private
def elabNonTerminals (nts : Array Syntax) : CommandElabM Unit := do
  -- Populate alias map immediately so we can resolve stuff within the current mutual throughout the
  -- following steps.
  let ns ← getCurrNamespace
  for nt in nts do
    let `(NonTerminal| $[nosubst]? nonterminal $[(parent := $parent?)]? $[(tex pre := $_, post := $_)]? $[$names],* := $_*) := nt
      | throwUnsupportedSyntax
    let names@(canonName :: _) := names.toList | throwUnsupportedSyntax
    let canon := ns ++ canonName.getId
    for name in names do
      setEnv <| aliasExt.addEntry (← getEnv) { canon, alias := ns ++ name.getId }

    if let some parent := parent? then
      let parent ← resolveSymbol parent (allowSuffix := false)
      setEnv <| childExt.addEntry (← getEnv) { canon, parent }

  -- Transform syntax into non-terminal structure.
  let nts ← nts.mapM fun nt => do
    let `(NonTerminal| $[nosubst%$ns]? nonterminal $[(parent := $parent?)]? $[(tex pre := $pre?, post := $post?)]? $[$names],* := $prods*) := nt
      | throwUnsupportedSyntax
    let some canon := names[0]? | throwUnsupportedSyntax
    let aliases := names.extract 1 names.size

    let prodAndSubsts ← prods.mapM fun prod => do
      let `(Production| | $[$ps]* : $name $[nosubst%$ns?]? $[notex%$nt?]? $[(bind $of? $[in $in??,*]?)]? $[(id $ids?,*)]? $[(expand := $expand?)]? $[(tex := $tex?)]?) := prod
        | throwUnsupportedSyntax
      let ids := ids?.getD (.mk #[]) |>.getElems

      let ir ← ps.mapM IR.ofProdArg
      let subst ← match ir with
        | #[mk _ (.category n)] =>
          if (metaVarExt.getState (← getEnv)).contains n then
            pure <| if ns?.isNone then some n else none
          else
            if let some ns := ns? then
              logWarningAt ns "unused nosubst; production is not a candidate for substitution"
            pure none
        | _ =>
          if let some ns := ns? then
            logWarningAt ns "unused nosubst; production is not a candidate for substitution"
          pure none

      let bindConfig? ← match of?, in?? with
        | some of, some in? => do
          let res := { of, in' := in?.getD (.mk #[]) : BindConfig }
          if let some x := ids.find? (res.find? ·.getId |>.isSome) then
            throwErrorAt x "name {x} also appears in bind config"
          for name in toStream res do
            if !containsName ir name.getId then
              logWarningAt name "name not found in syntax"
          pure <| some res
        | none, none => pure none
        | _, _ => unreachable!

      let ids := ids.map TSyntax.getId
      return (
        { name, ir, expand?, bindConfig?, ids, «notex» := nt?.isSome, tex? },
        subst
      )

    let (prods, substs) := prodAndSubsts.unzip
    let qualified := (← getCurrNamespace) ++ canon.getId
    let substitutions? := if parent?.isSome || ns.isSome then
        none
      else
        substs.filterMap id |>.map ((·, qualified))

    let parent? ← parent?.mapM fun parent =>
      return mkIdentFrom parent <| ← resolveSymbol parent (allowSuffix := false)

    let texPrePost? := match pre?, post? with
      | some pre, some post => some (pre.getString, post.getString)
      | none, none => none
      | _, _ => unreachable!

    return { canon, aliases, prods, parent?, substitutions?, texPrePost? : NonTerminal }

  -- Define mutual inductives and parser categories.
  let defsAndInductives ← nts.mapM fun nt@{ canon, prods, parent?, .. } => do
    setEnv <| ← registerParserCategory (← getEnv) (← nt.parserAttrName) (← nt.catName) .symbol
    setEnv <| ← registerParserCategory (← getEnv) (← nt.varParserAttrName) (← nt.varCatName) .symbol

    let some parent := parent? |
      let ctors ← prods.filterMapM fun prod@{ name, ir, expand?, ids, .. } => do
        let none := expand? | return none
        let ctorType ← IR.toTypeArrSeq ir canon ids prod.binders
        `(ctor| | $name:ident : $ctorType)
      let inductive' ← `(inductive $canon where $ctors*)
      return (none, inductive')
    let some { normalProds, .. } := symbolExt.getState (← getEnv) |>.find? parent.getId
      | throwErrorAt parent "unknown parent {parent.getId}"

    let isIdent := mkIdentFrom canon <| parent.getId ++ canon.getId.appendBefore "Is"
    let ctors ← prods.mapM fun prod@{ name, ir, expand?, .. } => match expand? with
      | some ref =>
        throwErrorAt ref "nonterminal with parent cannot contain productions with expand specifier"
      | none => do
        let some pir := normalProds.find? name.getId
          | throwErrorAt name "normal production with matching name not found in parent"

        IR.toIsChildCtor name isIdent (← nt.qualified) parent.getId ir pir prod.binders
    let inductive' ←
      `(inductive $(mkIdentFrom isIdent <| `_root_ ++ isIdent.getId) : $parent → Prop where
          $ctors*)

    return (some <| ← `(def $canon := { x : $parent // $isIdent x }), inductive')
  let (defs, inductives) := defsAndInductives.unzip
  elabMutualCommands inductives
  elabMutualCommands <| defs.filterMap id

  let ntsMap ← nts.foldlM (init := mkNameMap _) fun acc nt => return acc.insert (← nt.qualified) nt
  let namePairCmp | (a₁, a₂), (b₁, b₂) => Name.quickCmp a₁ b₁ |>.«then» <| Name.quickCmp a₂ b₂
  let nts ← nts.mapM fun nt => do
    if nt.substitutions?.isNone then
      return nt

    let mut substitutions' := RBTree.empty (cmp := namePairCmp)
    for n in ← nt.shallowClosure ntsMap do
      let substitutions? ← match ntsMap.find? n with
        | some { substitutions?, .. } => pure substitutions?
        | none =>
          let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n | continue
          pure substitutions
      let some substitutions := substitutions? | continue
      for subst in substitutions do
        substitutions' := substitutions'.insert subst
    return { nt with substitutions? := substitutions'.toArray : NonTerminal }

  for nt@{ canon, aliases, prods, parent?, substitutions?, texPrePost? } in nts do
    -- Add symbol to environment extension before proceeding so that lookups of things within the
    -- current mutual still work properly.
    let normalProds := prods.foldl (init := mkNameMap _) fun acc { name, ir, expand?, .. } =>
      if expand?.isNone then acc.insert name.getId ir else acc
    setEnv <| symbolExt.addEntry (← getEnv)
      { qualified := ← nt.qualified, normalProds, substitutions := substitutions?.getD #[], texPrePost? }

  let isLocallyNameless (varName : Name) : CommandElabM Bool :=
    return metaVarExt.getState (← getEnv) |>.find! varName

  for nt@{ canon, aliases, prods, parent?, substitutions?, .. } in nts do
    -- Define production and substitution parsers.
    let canonName := canon.getId
    let attrIdent := mkIdent <| ← nt.parserAttrName
    if parent?.isNone then
      for { name, ir, .. } in prods do
        let (val, type) ← IR.toParser ir nt.canon.getId symbolPrefix
        let parserIdent := mkIdentFrom name <| canonName ++ name.getId.appendAfter "_parser"
        elabCommand <| ←
          `(@[Lott.Symbol_parser, $attrIdent:ident]
            private
            def $parserIdent : $type := $val)

    let substitutions := substitutions?.getD #[]
    for (varName, valName) in substitutions do
      let parserIdent := mkIdent <| canonName ++ varName.appendAfter "_subst_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $attrIdent:ident]
          private
          def $parserIdent : TrailingParser :=
            trailingNode $(quote <| ← nt.catName) Parser.maxPrec 0 <|
              "[" >> categoryParser $(quote <| symbolPrefix ++ valName) 0 >> " / " >>
                categoryParser $(quote <| symbolPrefix ++ varName) 0 >> "]")

      -- Also add open parsers for this variable if it's locally nameless.
      if !(← isLocallyNameless varName) then
        continue

      let parserIdent := mkIdent <| canonName ++ varName.appendAfter "_open_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $attrIdent:ident]
          private
          def $parserIdent : TrailingParser :=
            trailingNode $(quote <| ← nt.catName) Parser.maxPrec 0 <|
              checkNoWsBefore >> "^" >> categoryParser $(quote <| symbolPrefix ++ varName) 0 >>
                Parser.optional (checkNoWsBefore >> "#" >> checkLineEq >> Parser.numLit))

      let parserIdent := mkIdent <| canonName ++ valName.appendAfter "_open_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $attrIdent:ident]
          private
          def $parserIdent : TrailingParser :=
            trailingNode $(quote <| ← nt.catName) Parser.maxPrec 0 <|
              checkNoWsBefore >> "^^" >> categoryParser $(quote <| symbolPrefix ++ valName) 0 >>
                Parser.optional (checkNoWsBefore >> "#" >> checkLineEq >> Parser.numLit) >>
                Parser.optional (checkNoWsBefore >> "/" >> checkLineEq >>
                  categoryParser $(quote <| symbolPrefix ++ varName) 0))

      let parserIdent := mkIdent <| canonName ++ varName.appendAfter "_close_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $attrIdent:ident]
          private
          def $parserIdent : Parser :=
            leadingNode $(quote <| ← nt.catName) Parser.maxPrec <|
              "\\" >> categoryParser $(quote <| symbolPrefix ++ varName) 0 >>
                Parser.optional (checkNoWsBefore >> "#" >> checkLineEq >> Parser.numLit) >>
                "^" >> categoryParser $(quote <| ← nt.catName) 0)

    -- Define variable parsers, plus variable category parser in symbol category.
    let varAttrIdent := mkIdent <| ← nt.varParserAttrName
    for alias in aliases do
      let aliasName@(.str .anonymous nameStr) := alias.getId | throwUnsupportedSyntax
      let parserIdent := mkIdentFrom alias <| canonName ++ aliasName.appendAfter "_parser"
      elabCommand <| ←
        `(@[$varAttrIdent:ident]
          private
          def $parserIdent : Parser :=
            leadingNode $(quote <| ← nt.varCatName) Parser.maxPrec <|
              Lott.identPrefix $(quote nameStr))

    let parserIdent := mkIdentFrom canon <| canon.getId.appendAfter "_idx_parser"
    elabCommand <| ←
      `(@[$varAttrIdent:ident]
        private
        def $parserIdent : TrailingParser :=
          trailingNode $(quote <| ← nt.varCatName) Parser.maxPrec 0 <|
            checkNoWsBefore >> "@" >> checkLineEq >> (Parser.ident <|> Parser.numLit))

    let varParserIdent := mkIdentFrom canon <| canonName.appendAfter "_variable_parser"
    elabCommand <| ←
      `(@[Lott.Symbol_parser, $attrIdent:ident]
        private
        def $varParserIdent : Parser :=
          leadingNode $(quote <| ← nt.catName) Parser.maxPrec <|
            categoryParser $(quote <| ← nt.varCatName) Parser.maxPrec)

    -- Define parser in parent.
    if let some parent := parent? then
      let parentQualified := parent.getId
      let parentParserCatName := symbolPrefix ++ parentQualified
      let parentParserAttrName := parentParserCatName.appendAfter "_parser"
      let parentParserIdent :=
        mkIdentFrom parent <| `_root_ ++ parentQualified ++ canonName.appendAfter "_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $(mkIdent parentParserAttrName):ident]
          private
          def $parentParserIdent : Parser :=
            leadingNode $(quote parentParserCatName) Parser.maxPrec <|
              categoryParser $(quote <| ← nt.catName) 0)

    -- Define macros and tex elaborations.
    let catName ← nt.catName
    let catIdent := mkIdent catName
    for prod@{ name, ir, expand?, ids, tex?, .. } in prods do
      let patternArgs ← IR.toPatternArgs ir

      let macroSeqItems ← IR.toMacroSeqItems ir canon.getId ids prod.binders
      let rest ← expand?.getDM do
        let exprArgs ← IR.toExprArgs ir ids prod.binders
        `(return Syntax.mkCApp $(quote <| ns ++ canonName ++ name.getId) #[$exprArgs,*])

      let macroName := mkIdentFrom name <| canonName ++ name.getId.appendAfter "Impl"
      elabCommand <| ←
        `(@[macro $symbolEmbedIdent]
          private
          def $macroName : Macro := fun stx => do
            let Lean.Syntax.node _ ``Lott.symbolEmbed #[
              Lean.Syntax.atom _ "[[",
              Lean.Syntax.node _ $(quote catName) #[$patternArgs,*],
              Lean.Syntax.atom _ "]]"
            ] := stx | Macro.throwUnsupported
            $macroSeqItems*
            $rest:term)

      let texSeqItems ← IR.toTexSeqItems ir canon.getId
      let rest ← tex?.getDM do
        let joinArgs := IR.toJoinArgs ir
        `(" ".intercalate [$joinArgs,*])

      let texElabName := mkIdentFrom name <| canonName ++ name.getId.appendAfter "TexElab"
      elabCommand <| ←
        `(@[lott_tex_elab $catIdent]
          private
          def $texElabName : TexElab := fun ref stx => do
            let Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] := stx
              | throwUnsupportedSyntax
            $texSeqItems*
            return $rest)

    if let some parent := parent? then
      let qualified ← nt.qualified
      let parentCatName := symbolPrefix ++ parent.getId
      let parentCatIdent := mkIdent parentCatName
      let parentMacroName :=
        mkIdent <| `_root_ ++ parent.getId ++ canon.getId.appendAfter "Impl"
      elabCommand <| ←
        `(@[macro $symbolEmbedIdent]
          private
          def $parentMacroName : Macro := fun stx => do
            let Lean.Syntax.node _ ``Lott.symbolEmbed #[
              Lean.Syntax.atom _ "[[",
              Lean.Syntax.node _ $(quote parentCatName) #[
                stx@(Lean.Syntax.node _ $(quote catName) _)
              ],
              Lean.Syntax.atom _ "]]"
            ] := stx | Macro.throwUnsupported
            return Lean.Syntax.mkCApp ``Subtype.val #[
              Lean.Syntax.mkTypeAscription (Lott.Syntax.mkSymbolEmbed stx) <|
                Lean.mkIdent $(quote qualified)
            ])

  -- Add metavar functions.
  let allSubstitutions := nts.map (·.substitutions?.getD #[])
  let uniqueSubstitutions :=
    allSubstitutions.flatten.foldl Std.HashSet.insert Std.HashSet.empty |>.toArray
  for subst@(varTypeName, valTypeName) in uniqueSubstitutions do
    let locallyNameless ← isLocallyNameless varTypeName

    let varTypeId := mkIdent <| if locallyNameless then
        varTypeName.appendAfter "Id"
      else
        varTypeName
    let valTypeId := mkIdent valTypeName

    let varId ← mkFreshIdent varTypeId
    let valId ← mkFreshIdent valTypeId

    let substDefs ← nts.filterMapM fun nt@{ canon, prods, substitutions?, .. } => do
      if !(substitutions?.getD #[]).contains subst then
        return none

      let matchAlts ← prods.filterMapM fun { name, ir, expand?, bindConfig?, .. } => do
        let none := expand? | return none
        let prodId := mkIdent <| canon.getId ++ name.getId

        let bindOf? := bindConfig?.map fun { of, .. } => of
        let binderId? ← bindConfig?.bindM fun bindConfig@{ of, .. } =>
          ir.findSomeM? fun (mk l ir) => do
            match ir with
            | .category n => return if n == varTypeName && l == of then some l else none
            | .atom _ =>
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "atoms shouldn't be referenced by binders"

              return none
            | .sepBy ..
            | .optional _ =>
              throwError "bind configuration for productions with sepBy or optional syntax are not supported"

        if let #[mk l (.category n)] := ir then
          if some l != binderId? && n == varTypeName then
            let lhs ← if locallyNameless then `(.free $varId) else pure varId
            return ← `(matchAltExpr| | $prodId $l => if $lhs = $l then $valId else $prodId $l)

        let some (patternArgs, rhsArgs) ←
          toSubstPatternAndArgs ir varTypeName valTypeName varId valId bindOf? binderId? |
          `(matchAltExpr| | x@($prodId ..) => x)

        `(matchAltExpr| | $prodId $patternArgs* => $prodId $rhsArgs*)

      return some <| ←
        `(def $(mkIdentFrom canon <| canon.getId ++ (← substName varTypeName))
            (x : $canon) ($varId : $varTypeId) ($valId : $valTypeId) : $canon := match x with
            $matchAlts:matchAlt*)

    elabMutualCommands substDefs

    if !locallyNameless then
      continue

    let idxId ← mkFreshIdent varTypeId

    let varOpenDefs ← nts.filterMapM fun nt@{ canon, prods, substitutions?, .. } => do
      if !(substitutions?.getD #[]).contains subst then
        return none

      let matchAlts ← prods.filterMapM fun { name, ir, expand?, bindConfig?, .. } => do
        let none := expand? | return none
        let prodId := mkIdent <| canon.getId ++ name.getId

        let bindOf? := bindConfig?.map fun { of, .. } => of
        let binderId? ← bindConfig?.bindM fun bindConfig@{ of, .. } =>
          ir.findSomeM? fun (mk l ir) => do
            match ir with
            | .category n => return if n == varTypeName && l == of then some l else none
            | .atom _ =>
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "atoms shouldn't be referenced by binders"

              return none
            | .sepBy ..
            | .optional _ =>
              throwError "bind configuration for productions with sepBy or optional syntax are not supported"

        let some (patternArgs, rhsArgs) ←
          toVarOpenPatternAndArgs ir varTypeName valTypeName varId idxId bindOf? binderId? |
          `(matchAltExpr| | x@($prodId ..) => x)

        if binderId?.isSome then
          `(matchAltExpr|
              | x@($prodId $patternArgs*) => let $idxId := $idxId + 1; $prodId $rhsArgs*)
        else
          `(matchAltExpr| | $prodId $patternArgs* => $prodId $rhsArgs*)

      return some <| ←
        `(def $(mkIdentFrom canon <| canon.getId ++ (← openName varTypeName))
            (x : $canon) ($varId : $varTypeId) ($idxId : Nat := 0) : $canon := match x with
            $matchAlts:matchAlt*)

    elabMutualCommands varOpenDefs

    let valOpenDefs ← nts.filterMapM fun nt@{ canon, prods, substitutions?, .. } => do
      if !(substitutions?.getD #[]).contains subst then
        return none

      let matchAlts ← prods.filterMapM fun { name, ir, expand?, bindConfig?, .. } => do
        let none := expand? | return none
        let prodId := mkIdent <| canon.getId ++ name.getId

        let bindOf? := bindConfig?.map fun { of, .. } => of
        let binderId? ← bindConfig?.bindM fun bindConfig@{ of, .. } =>
          ir.findSomeM? fun (mk l ir) => do
            match ir with
            | .category n => return if n == varTypeName && l == of then some l else none
            | .atom _ =>
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "atoms shouldn't be referenced by binders"

              return none
            | .sepBy ..
            | .optional _ =>
              throwError "bind configuration for productions with sepBy or optional syntax are not supported"

        if let #[mk l (.category n)] := ir then
          if some l != binderId? && n == varTypeName then
            return ← `(matchAltExpr| | $prodId $l => if .bound $idxId = $l then $valId else $prodId $l)

        let some (patternArgs, rhsArgs) ←
          toValOpenPatternAndArgs ir varTypeName valTypeName valId idxId bindOf? binderId? |
          `(matchAltExpr| | x@($prodId ..) => x)

        if binderId?.isSome then
          `(matchAltExpr|
              | x@($prodId $patternArgs*) => let $idxId := $idxId + 1; $prodId $rhsArgs*)
        else
          `(matchAltExpr| | $prodId $patternArgs* => $prodId $rhsArgs*)

      return some <| ←
        `(def $(mkIdentFrom canon <| canon.getId ++ (← openName valTypeName))
            (x : $canon) ($valId : $valTypeId) ($idxId : Nat := 0) : $canon := match x with
            $matchAlts:matchAlt*)

    elabMutualCommands valOpenDefs

    let closeDefs ← nts.filterMapM fun nt@{ canon, prods, substitutions?, .. } => do
      if !(substitutions?.getD #[]).contains subst then
        return none

      let matchAlts ← prods.filterMapM fun { name, ir, expand?, bindConfig?, .. } => do
        let none := expand? | return none
        let prodId := mkIdent <| canon.getId ++ name.getId

        let bindOf? := bindConfig?.map fun { of, .. } => of
        let binderId? ← bindConfig?.bindM fun bindConfig@{ of, .. } =>
          ir.findSomeM? fun (mk l ir) => do
            match ir with
            | .category n => return if n == varTypeName && l == of then some l else none
            | .atom _ =>
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "atoms shouldn't be referenced by binders"

              return none
            | .sepBy ..
            | .optional _ =>
              throwError "bind configuration for productions with sepBy or optional syntax are not supported"

        let some (patternArgs, rhsArgs) ←
          toClosePatternAndArgs ir varTypeName valTypeName varId idxId bindOf? binderId? |
          `(matchAltExpr| | x@($prodId ..) => x)

        if binderId?.isSome then
          `(matchAltExpr|
              | x@($prodId $patternArgs*) => let $idxId := $idxId + 1; $prodId $rhsArgs*)
        else
          `(matchAltExpr| | $prodId $patternArgs* => $prodId $rhsArgs*)

      return some <| ←
        `(def $(mkIdentFrom canon <| canon.getId ++ (← closeName varTypeName))
            (x : $canon) ($varId : $varTypeId) ($idxId : Nat := 0) : $canon := match x with
            $matchAlts:matchAlt*)

    elabMutualCommands closeDefs

    let freeDefs ←
      nts.filterMapM fun nt@{ canon, prods, substitutions?, .. } => do
        if !(substitutions?.getD #[]).contains subst then
          return none

        let freeId := mkIdent <| ← freeName varTypeName <| ← nt.qualified
        let matchAlts ← prods.filterMapM fun prod@{ name, ir, expand?, .. } => do
          let none := expand? | return none
          let prodId := mkIdentFrom name <| (← nt.qualified) ++ name.getId
          toFreeMatchAlt prodId ir subst prod.binders
        return some <| ← `(def $freeId : $canon → List $varTypeId $matchAlts:matchAlt*)

    elabMutualCommands freeDefs

    let locallyClosedInductives ← nts.filterMapM fun nt@{ canon, prods, substitutions?, .. } => do
      if !(substitutions?.getD #[]).contains subst then
        return none

      let locallyClosedId := mkIdent <| ← locallyClosedName varTypeName <| ← nt.qualified
      let ctors ← prods.mapM fun prod@{ name, ir, expand?, ids, .. } => do
        let none := expand? | return #[]
        toLocallyClosedCtors name locallyClosedId idxId (← nt.qualified) ir subst ids prod.binders
      return some <| ←
        `(inductive $locallyClosedId : $canon → (optParam Nat 0) → Prop where $ctors.flatten*)

    elabMutualCommands locallyClosedInductives

  -- Write tex output.
  for nt@{ canon, aliases, prods, .. } in nts do
    writeTexOutput (ns ++ canon.getId) do
      let canonTex := canon.getId.getFinal.getString!.pascalToTitle.texEscape
      let aliasesTex := "\\lottaliassep".intercalate <|
        aliases.toList.map (s!"\\lottalias\{{·.getId.getFinal.getString!.texEscape}}")
      let productionTexs ← prods.filterMapM fun { name, ir, «notex», .. } => do
        if «notex» then return none

        let canonQualified := ns ++ canon.getId
        let catName ← nt.catName
        let exampleStx := mkNode catName <| ← IR.toExampleSyntax ir canonQualified
        let productionTex ← liftTermElabM <| texElabSymbolOrJudgement catName name exampleStx
        return some s!"\\lottproduction\{{productionTex}}"
      let productionsTex := "\\lottproductionsep".intercalate productionTexs.toList
      return s!"\\lottnonterminal\{{canonTex}}\{{aliasesTex}}\{{productionsTex}}\n"


elab_rules : command
  | `($nt:Lott.NonTerminal) => elabNonTerminals #[nt]
  | `(mutual $[$nts:Lott.NonTerminal]* end) => elabNonTerminals nts

/- Judgement syntax. -/

elab_rules : command | `(judgement_syntax $[$ps]* : $name $[(id $ids?,*)]? $[(tex := $tex?)]?) => do
  -- Declare syntax category.
  let ns ← getCurrNamespace
  let qualified := ns ++ name.getId
  let catName := judgementPrefix ++ qualified
  let parserAttrName := catName.appendAfter "_parser"
  setEnv <| ← Parser.registerParserCategory (← getEnv) parserAttrName catName .symbol

  -- Add to environment extension.
  let ir ← ps.mapM IR.ofStx
  let ids := ids?.getD (.mk #[]) |>.getElems |>.map TSyntax.getId
  setEnv <| judgementExt.addEntry (← getEnv) { name := qualified, ir, ids }

  -- Declare parser.
  let (val, type) ← IR.toParser ir name.getId judgementPrefix
  if type != (← `(term| Parser)) then throwError "invalid left recursive judgement syntax"
  let parserIdent := mkIdentFrom name <| name.getId.appendAfter "_parser"
  elabCommand <| ←
    `(@[Lott.Judgement_parser, $(mkIdent parserAttrName):ident]
      private
      def $parserIdent : Parser := $val)

  -- Define macro.
  let patternArgs ← IR.toPatternArgs ir

  let macroSeqItems ← IR.toMacroSeqItems ir name.getId ids #[]
  let exprArgs ← IR.toExprArgs ir ids #[]
  let catIdent := mkIdent catName

  let macroName := mkIdentFrom name <| name.getId.appendAfter "Impl"
  elabCommand <| ←
    `(@[macro $(mkIdent `Lott.judgementEmbed)]
      private
      def $macroName : Macro := fun stx => do
        let Lean.Syntax.node _ ``Lott.judgementEmbed #[
          Lean.Syntax.atom _ "[[",
          Lean.Syntax.node _ $(quote catName) #[$patternArgs,*],
          Lean.Syntax.atom _ "]]"
        ] := stx | Macro.throwUnsupported
        $macroSeqItems*
        return Syntax.mkApp (mkIdent $(quote qualified)) #[$exprArgs,*])

  let texSeqItems ← IR.toTexSeqItems ir name.getId
  let rest ← tex?.getDM do
    let joinArgs := IR.toJoinArgs ir
    `(term| " ".intercalate [$joinArgs,*])

  let texElabName := mkIdentFrom name <| name.getId.appendAfter "TexElab"
  elabCommand <| ←
    `(@[lott_tex_elab $catIdent]
      private
      def $texElabName : TexElab := fun ref stx => do
        let Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] := stx
          | throwUnsupportedSyntax
        $texSeqItems*
        return $rest)

private
def elabJudgementDecls (jds : Array Syntax) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let inductives ← jds.mapM fun jd => do
    let `(JudgementDecl| judgement $name := $rules*) := jd | throwUnsupportedSyntax

    let qualified := ns ++ name.getId
    let .some { ir, ids, .. } := judgementExt.getState (← getEnv) |>.byName.find? qualified
      | throwError "judgement_syntax for {name} not given before use in judgement"

    let type ← IR.toTypeArrSeq ir (← `(term| Prop)) ids #[]
    let catName := judgementPrefix ++ qualified
    let ctors ← rules.mapM fun rule => do
      let `(InferenceRule| $hyps:Lott.Judgement* $[─]* $name $binders* $[notex%$nt?]? $conclusion:Lott.Judgement) := rule
        | throwUnsupportedSyntax
      let conclusionKind := conclusion.raw.getKind
      if conclusionKind != catName then
        throwErrorAt conclusion
          "found conclusion judgement syntax kind{indentD conclusionKind}\
          expected to find kind{indentD catName}\
          all conclusions of inference rules in a judgement declaration must be the judgement which is being defined"

      let ctorType ← hyps.foldrM (init := ← `(term| [[$conclusion:Lott.Judgement]]))
        fun «judgement» acc => `([[$«judgement»:Lott.Judgement]] → $acc)
      `(ctor| | $name:ident $binders* : $ctorType)

    writeTexOutput qualified do
      let nameTex := name.getId.getFinal.getString!.pascalToTitle.texEscape
      let exampleStx := mkNode catName <| ← IR.toExampleSyntax ir qualified
      let syntaxTex ← liftTermElabM <| texElabSymbolOrJudgement catName name exampleStx
      let inferenceRuleTexs ← rules.filterMapM fun rule => do
        let `(InferenceRule| $hyps:Lott.Judgement* $[─]* $name $_* $[notex%$nt?]? $conclusion:Lott.Judgement) := rule
          | throwUnsupportedSyntax

        if nt?.isSome then
          return none

        let nameTex := name.getId.getFinal.getString!.texEscape
        let hypothesesTexs ← hyps.filterMapM fun
          | `(Judgement| $_:Lott.Judgement notex) => return none
          | hyp => do
            let hypTex ← liftTermElabM <| texElabSymbolOrJudgement hyp.getKind hyp hyp
            return s!"\\lotthypothesis\{{hypTex}}"
        let hypothesesTex := "\\lotthypothesissep".intercalate hypothesesTexs.toList
        let conclusionTex ← liftTermElabM <| texElabSymbolOrJudgement catName conclusion conclusion
        return s!"\\lottinferencerule\{{nameTex}}\{{hypothesesTex}}\{{conclusionTex}}"

      let inferenceRulesTex := "\\lottinferencerulesep".intercalate inferenceRuleTexs.toList
      return s!"\\lottjudgement\{{nameTex}}\{{syntaxTex}}\{{inferenceRulesTex}}\n"

    `(inductive $name : $type where $ctors*)
  elabMutualCommands inductives

elab_rules : command
  | `($jd:Lott.JudgementDecl) => elabJudgementDecls #[jd]
  | `(mutual $[$jds:Lott.JudgementDecl]* end) => elabJudgementDecls jds

/- Term embedding syntax. -/

@[macro qualifiedSymbolEmbed]
def qualifiedSymbolEmbedImpl : Macro := fun stx =>
  return Lott.Syntax.mkSymbolEmbed <| stx.getArg 3

/- External interaction syntax. -/

elab_rules : command
  | `(#filter $inputName:str $[$outputName?:str]?) => do
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

    -- TODO: Make the output path here relative if possible.
    writeMakeDeps outputName
    liftIO <| writeFile outputName <| String.join output.toList

end Lott
