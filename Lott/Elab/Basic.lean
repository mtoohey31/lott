import Lott.Data.Char
import Lott.Data.List
import Lott.Data.Name
import Lott.Data.Option
import Lott.Data.String
import Lott.Elab.Options
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
open Lean.Parser.Command
open Lean.Parser.Term
open Lott.IR
open System

/- Utility stuff. -/

def writeMakeDeps (filePath : FilePath) (extraDeps : List FilePath := []) : CommandElabM Unit := do
  if !(← getOptions).get lott.tex.output.makeDeps.name lott.tex.output.makeDeps.defValue then
    return

  let sp ← liftIO <| initSrcSearchPath
  let depPaths ← (← getEnv).allImportedModuleNames.mapM (findLean sp ·)
  let deps := " ".intercalate <| (depPaths.toList ++ extraDeps).map
    (·.toString.dropPrefixes "./" |>.toString)
  writeFile (filePath.addExtension "d")
    s!"{filePath.toString.dropPrefixes "./" |>.toString}: {deps}\n"

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

abbrev TexElab := (profile : Name) → (ref : Syntax) → Syntax → TermElabM String

private unsafe
def mkLottTexElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute TexElab) := do
  mkElabAttribute TexElab .anonymous `lott_tex_elab `Lott ``Lott.TexElab "lott" ref

@[implemented_by mkLottTexElabAttributeUnsafe]
opaque mkLottTexElabAttribute (ref : Name) : IO (KeyedDeclsAttribute TexElab)

initialize lottTexElabAttribute : KeyedDeclsAttribute TexElab ← mkLottTexElabAttribute decl_name%

def texElabIdx : Syntax → TermElabM String
  | .ident _ _ val _ => pure <| val.toString false |>.texEscape
  | .node _ `num #[.atom _ raw] => pure raw.texEscape
  | _ => throwUnsupportedSyntax

private
def texElabMetavar : TexElab := fun
  | _, _, .node _ catName #[.ident _ _ val _]
  | _, _, .node _ catName #[.ident _ _ val _, .atom _ "$", .node _ `num _] => do
    let ns ← getCurrNamespace
    let some qualified := catName.erasePrefix? symbolPrefix | throwUnsupportedSyntax

    let valString := val.toString false
    let some { canon, alias, tex? := some tex } :=
      aliasExt.getState (← getEnv) |>.byAlias.matchPrefix (ns ++ val).toString 0
      | return valString.texEscape
    if qualified != canon then
      return valString.texEscape
    let some aliasUnqualified := alias.erasePrefix? ns | return valString.texEscape
    let some suffix := valString.dropPrefix? <| aliasUnqualified.toString false
      | return valString.texEscape

    return tex ++ suffix.toString.texEscape
  | profile, ref, .node _ _ #[«fun», .atom _ "@", idx] => do
    let funTex ← texElabMetavar profile ref «fun»
    let idxTex ← texElabIdx idx
    return s!"\{{funTex}}_\{{idxTex}}"
  | _, _, _ => throwUnsupportedSyntax

mutual

private partial
def texElabVariable : TexElab := fun
  | _, _, .node _ catName #[.node _ _ #[.ident _ _ val _] ] => do
    let ns ← getCurrNamespace
    let some qualified := catName.erasePrefix? symbolPrefix | throwUnsupportedSyntax

    let valString := val.toString false
    let some { canon, alias, tex? := some tex } :=
      aliasExt.getState (← getEnv) |>.byAlias.matchPrefix (ns ++ val).toString 0
      | return valString.texEscape
    if qualified != canon then
      return valString.texEscape
    let some aliasUnqualified := alias.erasePrefix? ns | return valString.texEscape
    let some suffix := valString.dropPrefix? <| aliasUnqualified.toString false
      | return valString.texEscape

    return tex ++ suffix.toString.texEscape
  | profile, ref, .node info kind #[.node _ _ #[«fun», .atom _ "@", idx] ] => do
    let funTex ← texElabVariable profile ref <| .node info kind #[«fun»]
    let idxTex ← texElabIdx idx
    return s!"\{{funTex}}_\{{idxTex}}"
  | profile, ref, .node _ catName #[
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

    let baseTex ← texElabSymbolOrJudgement catName profile ref base
    let valTex ← texElabSymbolOrJudgement symbolPrefixedValName profile ref val
    let varTex ← texElabSymbolOrJudgement symbolPrefixedVarName profile ref var

    return s!"{baseTex}\\left[{valTex}/{varTex}\\right]"
  | profile, ref, .node _ catName #[
      base@(.node _ catName₀ _),
      .atom _ "^",
      var@(.node _ symbolPrefixedVarName _),
      .node _ `null level,
      node _ `null locallyNamelessSubstAlternative
    ] => do
    if catName != catName₀ then
      throwUnsupportedSyntax

    if !symbolPrefix.isPrefixOf catName then throwUnsupportedSyntax
    if !symbolPrefix.isPrefixOf symbolPrefixedVarName then throwUnsupportedSyntax

    let baseTex ← texElabSymbolOrJudgement catName profile ref base
    let varTex ← texElabSymbolOrJudgement symbolPrefixedVarName profile ref var

    if !(← getOptions).get lott.tex.locallyNameless.name lott.tex.locallyNameless.defValue then
      match locallyNamelessSubstAlternative with
      |  #[.atom _ "/", var@(.node _ symbolPrefixedVarName _)] =>
        if !symbolPrefix.isPrefixOf symbolPrefixedVarName then
          throwUnsupportedSyntax

        let oldVarTex ← texElabSymbolOrJudgement symbolPrefixedVarName profile ref var
        return s!"{baseTex}\\left[{varTex}/{oldVarTex}\\right]"
      | #[] => return baseTex
      | _ => throwUnsupportedSyntax

    if let some level := level[1]? then
      let levelTex ← texElabIdx level
      return s!"\{{baseTex}}^\{{varTex}#{levelTex}}"
    else
      return s!"\{{baseTex}}^\{{varTex}}"
  | profile, ref, .node _ catName #[
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

    let baseTex ← texElabSymbolOrJudgement catName profile ref base
    let valTex ← texElabSymbolOrJudgement symbolPrefixedValName profile ref val

    if !(← getOptions).get lott.tex.locallyNameless.name lott.tex.locallyNameless.defValue then
      let varTex ← match locallyNamelessSubstAlternative with
        |  #[.atom _ "/", var@(.node _ symbolPrefixedVarName _)] =>
          if !symbolPrefix.isPrefixOf symbolPrefixedVarName then
            throwUnsupportedSyntax

          texElabSymbolOrJudgement symbolPrefixedVarName profile ref var
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
  | profile, ref, .node _ catName #[
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

    let baseTex ← texElabSymbolOrJudgement catName profile ref base
    let varTex ← texElabSymbolOrJudgement symbolPrefixedVarName profile ref var

    if !(← getOptions).get lott.tex.locallyNameless.name lott.tex.locallyNameless.defValue then
      return s!"\{{baseTex}}"

    if let some level := level[1]? then
      let levelTex ← texElabIdx level
      return s!"\\leftidx\{{varTex}#{levelTex}}\{{baseTex}}\{}"
    else
      return s!"\\leftidx\{{varTex}}\{{baseTex}}\{}"
  | profile, ref, .node _ parentCatName #[stx@(.node _ childCatName _)] => do
    let some parentQualified := parentCatName.erasePrefix? symbolPrefix | throwUnsupportedSyntax
    let some childQualified := childCatName.erasePrefix? symbolPrefix | throwUnsupportedSyntax
    let some { parent, .. } := childExt.getState (← getEnv) |>.find? childQualified | throwUnsupportedSyntax
    if parent != parentQualified then throwUnsupportedSyntax

    texElabSymbolOrJudgement childCatName profile ref stx
  | _, _, _ => throwUnsupportedSyntax

partial
def texElabSymbolOrJudgement (catName : Name) (profile : Name) (ref stx : Syntax)
  : TermElabM String := do
  let env ← getEnv
  let texPrePost? := do
    let qualified ← catName.erasePrefix? symbolPrefix
    let { texPrePost?, .. } ← symbolExt.getState env |>.find? qualified
    texPrePost?

  let rawTex ← match lottTexElabAttribute.getEntries (← getEnv) catName with
    | [] =>
      try
        (try texElabMetavar profile ref stx catch _ => texElabVariable profile ref stx)
      catch _ =>
        throwErrorAt ref
          "tex elaboration function for '{catName}' has not been implemented{indentD stx}"
    | elabFns =>
      try texElabWithFns elabFns catch ex =>
        (try texElabMetavar profile ref stx catch _ =>
          (try texElabVariable profile ref stx catch _ => throw ex))

  if let some (texPre, texPost) := texPrePost? then
    return s!"{texPre} {rawTex} {texPost}"
  else
    return rawTex
where
  texElabWithFns
    | [] => unreachable!
    | [elabFn] => elabFn.value profile ref stx
    | elabFn :: elabFns => do
      try
        elabFn.value profile ref stx
      catch ex => match ex with
        | .internal id _ =>
          if id == unsupportedSyntaxExceptionId then texElabWithFns elabFns else throw ex
        | _ => throw ex

end

def elabMutualCommands (cs : Array Command) : CommandElabM Unit :=
  match cs with
  | #[] => pure ()
  | #[c] => elabCommand c
  | cs => do elabCommand <| ← `(mutual $cs* end)

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

partial
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

partial
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
                  _,
                  pat,
                  Lean.Syntax.atom _ "in",
                  collection,
                  _,
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
                  _,
                  cond,
                  _,
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

partial
def _root_.Lott.IR.toTexSeqItems (ir : Array IR) (canon : Name)
  : CommandElabM (TSyntaxArray ``Lean.Parser.Term.doSeqItem) :=
  ir.mapM fun
    | mk l (.category n) => do
      `(doSeqItem|
        let $l ← Lott.texElabSymbolOrJudgement $(quote <| symbolPrefix ++ n) profile ref $l)
    | mk l (.atom s) =>
      `(doSeqItem| let $l := $(quote <| atomToTex s))
    | mk l (.sepBy ir sep) => do
      let catName := sepByPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir canon
      let joinArgs := IR.toJoinArgs ir
      let go ← mkFreshIdent l

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx =>
            let rec $go:ident : Lean.Syntax → Lean.Elab.Term.TermElabM String
              | Lean.Syntax.node _ $(quote catName) #[
                  Lean.Syntax.atom _ "</",
                  symbol,
                  Lean.Syntax.atom _ "//",
                  tex,
                  pat,
                  Lean.Syntax.atom _ "in",
                  collection,
                  «notex»,
                  Lean.Syntax.atom _ "/>"
                ] => do
                let symbolTex ← $go:ident symbol
                if «notex».getNumArgs == 1 then
                  return s!"\\lottsepbycomprehension\{{symbolTex}}"

                if let some tex := tex.getArgs[3]? then
                  let customTex := tex.isStrLit?.getD ""
                  return s!"\\lottsepbycomprehensioncustom\{{symbolTex}}\{{customTex}}"

                let some patSubstring :=
                  pat.getSubstring? (withLeading := false) (withTrailing := false)
                  | throwUnsupportedSyntax
                let patTex := patSubstring.toString.texEscape
                let some collectionSubstring :=
                  collection.getSubstring? (withLeading := false) (withTrailing := false)
                  | throwUnsupportedSyntax
                let collectionTex := collectionSubstring.toString.texEscape
                return s!"\\lottsepbycomprehensionpatcollection\{{symbolTex}}\{{patTex}}\{{collectionTex}}"
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
            $go:ident stx
          | none => pure "")
    | mk l (.optional ir) => do
      let catName := optionalPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir canon
      let joinArgs := IR.toJoinArgs ir
      let go ← mkFreshIdent l

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx =>
            let rec $go:ident : Lean.Syntax → Lean.Elab.Term.TermElabM String
              | Lean.Syntax.node _ $(quote catName) #[
                  Lean.Syntax.atom _ "</",
                  symbol,
                  Lean.Syntax.atom _ "//",
                  tex,
                  cond,
                  «notex»,
                  Lean.Syntax.atom _ "/>"
                ] => do
                let symbolTex ← $go:ident symbol
                if «notex».getNumArgs == 1 then
                  return s!"\\lottoptionalcomprehension\{{symbolTex}}"

                if let some tex := tex.getArgs[3]? then
                  let customTex := tex.isStrLit?.getD ""
                  return s!"\\lottoptionalcomprehensioncustom\{{symbolTex}}\{{customTex}}"

                let some condSubstring :=
                  cond.getSubstring? (withLeading := false) (withTrailing := false)
                  | throwUnsupportedSyntax
                let condTex := condSubstring.toString.texEscape
                return s!"\\lottoptionalcomprehensioncond\{{symbolTex}}\{{condTex}}"
              | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
                $seqItems*
                return " ".intercalate [$joinArgs,*]
              | _ => Lean.Elab.throwUnsupportedSyntax
            $go:ident stx
          | none => pure "")
where
  atomToTex (atom : String) :=
    let leadingWs := atom.data[0]?.map Char.isWhitespace |>.getD false
    let trailingWs := atom.data.getLast?.map Char.isWhitespace |>.getD false
    let tex := if atom.trim.data.all (fun c => c.isAlpha || c.isSubscriptAlpha) then
        s!"\\lottkw\{{atom.trim.texEscape}}"
      else
        s!"\\lottsym\{{atom.trim.texEscape}}"
    (if leadingWs then "\\, " else "") ++ tex ++ (if trailingWs then " \\," else "")

partial
def toExampleSyntax (ir : Array IR) (canonQualified profile : Name) (enclosingSepBys := 0)
  : CommandElabM (Array Syntax) := do
  let inline := (← getOptions).get lott.tex.example.singleProductionInline.name
    lott.tex.example.singleProductionInline.defValue
  let «notex» := (← getOptions).get lott.tex.example.comprehensionNoTex.name
    lott.tex.example.comprehensionNoTex.defValue
  ir.mapM fun (mk l ir) => match ir with
    | .category n => do
      let env ← getEnv
      if metaVarExt.getState env |>.contains n then
        return sepByIdxStrings.foldl (init := mkNode (symbolPrefix ++ n) #[l])
          (stop := enclosingSepBys)
          (mkNode (symbolPrefix ++ n) #[·, mkAtom "@", mkIdent <| .str .anonymous ·])

      if inline then
        if let some { normalProds, .. } := symbolExt.getState env |>.find? n then
          if normalProds.size == 1 then
            return mkNode (symbolPrefix ++ n) <|
              ← toExampleSyntax normalProds.toArray[0]!.snd n profile enclosingSepBys

      return mkNode (symbolPrefix ++ n) #[
        sepByIdxStrings.foldl (init := mkNode (variablePrefix ++ n) #[l]) (stop := enclosingSepBys)
          (mkNode (variablePrefix ++ n) #[·, mkAtom "@", mkIdent <| .str .anonymous ·])
      ]
    | .atom s => return mkAtom s.trim
    | .sepBy ir _ => do
      let catName := sepByPrefix ++ canonQualified ++ l.getId |>.obfuscateMacroScopes
      let some patString := sepByIdxStrings[enclosingSepBys]?
        | throwError "encountered too many nested sepBys; ran out of index names"
      let collectionString := "[:n]"
      return mkNullNode #[
        mkNode catName #[
          mkAtom "</",
          mkNode catName <| ← toExampleSyntax ir canonQualified profile enclosingSepBys.succ,
          mkAtom "//",
          mkNullNode,
          .ident (.original ⟨patString, 0, 0⟩ 0 ⟨patString, ⟨1⟩, ⟨1⟩⟩ ⟨1⟩)
            patString.toSubstring `i [],
          mkAtom "in",
          .node (.original ⟨collectionString, ⟨0⟩, ⟨0⟩⟩ ⟨0⟩ ⟨collectionString, ⟨4⟩, ⟨4⟩⟩ ⟨4⟩)
            ``Std.Range.«term[:_]» #[
              .atom (.original ⟨collectionString, ⟨0⟩, ⟨0⟩⟩ ⟨0⟩ ⟨collectionString, ⟨1⟩, ⟨1⟩⟩ ⟨1⟩)
                "[",
              .atom (.original ⟨collectionString, ⟨1⟩, ⟨1⟩⟩ ⟨1⟩ ⟨collectionString, ⟨2⟩, ⟨2⟩⟩ ⟨2⟩)
                ":",
              .ident (.original ⟨collectionString, ⟨2⟩, ⟨2⟩⟩ ⟨2⟩ ⟨collectionString, ⟨3⟩, ⟨3⟩⟩ ⟨3⟩)
                ⟨collectionString, ⟨2⟩, ⟨3⟩⟩ `n [],
              .atom (.original ⟨collectionString, ⟨3⟩, ⟨3⟩⟩ ⟨3⟩ ⟨collectionString, ⟨4⟩, ⟨4⟩⟩ ⟨4⟩)
                "]"
          ],
          mkNullNode <| Option.someIf (mkAtom "notex") «notex» |>.toArray,
          mkAtom "/>"
        ]
      ]
    | .optional ir => do
      let catName := optionalPrefix ++ canonQualified ++ l.getId |>.obfuscateMacroScopes
      let condString := "b"
      return mkNullNode #[
        mkNode catName #[
          mkAtom "</",
          mkNode catName <| ← toExampleSyntax ir canonQualified profile enclosingSepBys,
          mkAtom "//",
          mkNullNode,
          .ident (.original ⟨condString, 0, 0⟩ 0 ⟨condString, ⟨1⟩, ⟨1⟩⟩ ⟨1⟩)
            condString.toSubstring `b [],
          mkNullNode <| Option.someIf (mkAtom "notex") «notex» |>.toArray,
          mkAtom "/>"
        ]
      ]
where
  sepByIdxStrings := #["i", "j", "k", "l", "m"]

/- Conditional syntax. -/

elab_rules : command | `(termonly $c) => do if ← getTerm then elabCommand c

/- Term embedding syntax. -/

@[macro qualifiedSymbolEmbed]
def qualifiedSymbolEmbedImpl : Macro := fun stx =>
  return Lott.Syntax.mkSymbolEmbed <| stx.getArg 3

end Lott
