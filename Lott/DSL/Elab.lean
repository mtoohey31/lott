import Lean.Elab.Syntax
import Lott.DSL.Environment
import Lott.DSL.Parser

namespace Lott.DSL

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Syntax
open Lean.Parser
open Lean.Parser.Command
open Lean.Parser.Syntax
open Lean.Parser.Term

/- Term embedding syntax. -/

abbrev LottElab := Syntax → TermElabM Expr

private unsafe
def mkLottElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute LottElab) := do
  mkElabAttribute LottElab .anonymous `lott_elab `Lott `Lott.DSL.LottElab "lott" ref

@[implemented_by mkLottElabAttributeUnsafe]
opaque mkLottElabAttribute (ref : Name) : IO (KeyedDeclsAttribute LottElab)

initialize lottElabAttribute : KeyedDeclsAttribute LottElab ← mkLottElabAttribute decl_name%

/- Utility stuff. -/

private
def resolveSymbol (symbolName : TSyntax `ident) : CommandElabM Name := do
  let name := symbolName.getId
  let state := lottSymbolAliasExt.getState (← getEnv)

  -- First check if the name itself is present in the state.
  if let some { canon, .. } := state.byAlias.find? name then
    return canon

  -- If not, check if it's present when prepending the current namespace.
  if let some { canon, .. } := state.byAlias.find? <| (← getCurrNamespace) ++ name then
    return canon

  -- Otherwise, check the namespaces we've opened.
  resolveWithOpens name state (← getOpenDecls)
where
  resolveWithOpens name state
    | [] => throwErrorAt symbolName "unknown lott symbol {symbolName}"
    | .simple ns except :: decls => do
      if !except.contains name then
        if let some { canon, .. } := state.byAlias.find? <| ns ++ name then
          return canon
      resolveWithOpens name state decls
    | .explicit id declName :: decls => do
      if id = name then
        if let some { canon, .. } := state.byAlias.find? declName then
          return canon
      resolveWithOpens name state decls

private
def symbolPrefix := `Lott.Symbol

private
def variablePrefix := `Lott.Variable

private
def judgementPrefix := `Lott.Judgement

/- Metavariable syntax. -/

elab_rules : command | `(metavar $names,*) => do
  let names := names.getElems.toList
  let canon :: aliases := names | throwUnsupportedSyntax
  let ns ← getCurrNamespace
  let canonQualified := ns ++ canon.getId

  -- Declare type and aliases.
  -- TODO: Is there any way we can make these have an opaque type which reveals nothing other than
  -- that they have a decidable equality relation?
  elabCommand <| ← `(def $canon := Nat)
  for name in names do
    setEnv <| lottSymbolAliasExt.addEntry (← getEnv)
      { canon := canonQualified, alias := ns ++ name.getId }
  elabCommand <| ← `(instance (x y : $canon) : Decidable (x = y) := Nat.decEq x y)

  -- Declare syntax category. For metavariables we just declare the alias name parsers directly in
  -- the syntax category. This differs from variable parsers for non-terminals, for which we declare
  -- a separate variable category, then add a category parser for the variable category to the main
  -- non-terminal symbol category.
  let catName := symbolPrefix ++ canonQualified
  let attrName := catName.appendAfter "_parser"
  setEnv <| ← Parser.registerParserCategory (← getEnv) attrName catName .symbol

  -- Declare parsers in category.
  let attrIdent := mkIdent attrName
  for alias in aliases do
    let aliasName@(.str .anonymous nameStr) := alias.getId | throwUnsupportedSyntax
    let parserIdent := mkIdentFrom alias <| canon.getId ++ aliasName.appendAfter "_parser"
    elabCommand <| ←
      `(@[$attrIdent:ident] def $parserIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <|
            Lott.DSL.identPrefix $(quote nameStr))

  -- Define elaboration.
  let catIdent := mkIdentFrom canon catName
  let termElabName := mkIdentFrom canon <| canon.getId.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_elab $catIdent] def $termElabName : Lott.DSL.LottElab
        | Lean.Syntax.node _ $(quote catName) #[ident@(Lean.Syntax.ident ..)] => do
          let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
          Lean.Elab.Term.elabTerm ident type
        | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

/- Term embedding syntax. -/

partial
def elabTerm (catName : Name) : LottElab := fun stx => do
  let result ← liftMacroM <| expandMacroImpl? (← getEnv) stx
  match result with
  | some (decl, stxNew?) => do
    let stxNew ← liftMacroM <| liftExcept stxNew?
    withInfoContext' stx (mkInfo := mkTermInfo decl stx) <|
      withMacroExpansion stx stxNew <|
        withRef stxNew <|
          elabTerm catName stxNew
  | none =>
    match lottElabAttribute.getEntries (← getEnv) catName with
    | [] =>
      throwError "term elaboration function for '{catName}' has not been implemented{indentD stx}"
    | elabFns => elabTermWithFns stx elabFns
where
  elabTermWithFns stx
    | [] => unreachable!
    | [elabFn] => elabFn.value stx
    | elabFn :: elabFns => do
      try
        elabFn.value stx
      catch ex => match ex with
        | .internal id _ =>
          if id == unsupportedSyntaxExceptionId then
            elabTermWithFns stx elabFns
          else
            throw ex
        | _ => throw ex

@[term_elab lott_symbol_embed]
private
def symbolEmbedElab : TermElab := fun stx _ => do
  let stx := stx[3]!
  elabTerm stx.getKind stx

elab_rules : term
  | `([[$stx:Lott.Symbol]]) => elabTerm stx.raw.getKind stx
  | `([[$stx:Lott.Judgement]]) => elabTerm stx.raw.getKind stx

/- Non-terminal syntax. -/

private
def elabNonTerminals (nts : Array Syntax) : CommandElabM Unit := do
  -- Populate alias map immediately so we can resolve stuff within the current mutual throughout the
  -- following steps.
  let ns ← getCurrNamespace
  for nt in nts do
    let `(NonTerminal| nonterminal $[$names],* := $_*) := nt | throwUnsupportedSyntax
    let names := names.toList
    let canonName :: _ := names | throwUnsupportedSyntax
    for name in names do
      setEnv <| lottSymbolAliasExt.addEntry (← getEnv)
        { canon := ns ++ canonName.getId, alias := ns ++ name.getId }

  -- Define mutual inductives and parser categories.
  let catOfName (name : TSyntax `ident) := symbolPrefix ++ ns ++ name.getId
  let varCatOfName (name : TSyntax `ident) := variablePrefix ++ ns ++ name.getId
  let attrOfName name := catOfName name |>.appendAfter "_parser"
  let varAttrOfName name := varCatOfName name |>.appendAfter "_parser"
  let inductives ← nts.mapM fun nt => do
    let `(NonTerminal| nonterminal $[$names],* := $prods*) := nt | throwUnsupportedSyntax
    let some name := names.get? 0 | throwUnsupportedSyntax

    let env' ← registerParserCategory (← getEnv) (attrOfName name) (catOfName name) .symbol
    setEnv <| ← registerParserCategory env' (varAttrOfName name) (varCatOfName name) .symbol

    let ctors ← prods.filterMapM fun stx => do
      let `(Production| | $[$ps]* : $prodIdent $[$desugarConfig?]? $[$elabConfig?]?) := stx
        | throwUnsupportedSyntax
      if desugarConfig?.isSome || elabConfig?.isSome then return none
      let ctorType ← ps.foldrM (init := name) fun
        | `($name:ident), acc => do `($(mkIdentFrom name (← resolveSymbol name)) → $acc)
        | _, acc => return acc
      `(ctor| | $prodIdent:ident : $ctorType)
    `(inductive $name where $ctors*)
  elabCommand <| ← `(mutual $inductives* end)

  for nt in nts do
    let `(NonTerminal| nonterminal $[$names],* := $prods*) := nt | throwUnsupportedSyntax
    let canon :: aliases := names.toList | throwUnsupportedSyntax

    -- Define production parsers.
    let canonName := canon.getId
    let catName := catOfName canon
    let attrIdent := mkIdent <| attrOfName canon
    for prod in prods do
      let `(Production| | $[$ps]* : $prodIdent $[$desugarConfig?]? $[$elabConfig?]?) := prod
        | throwUnsupportedSyntax

      let ps ← ps.mapM (β := Syntax) fun
        | `($name:ident) => do
          `(cat| $(mkIdentFrom name <| symbolPrefix ++ (← resolveSymbol name)):ident)
        | other => return other
      let (val, lhsPrec?) ← liftTermElabM <| toParserDescr (mkNullNode ps) catName
      let parserIdent := mkIdentFrom prodIdent <| canonName ++ prodIdent.getId |>.appendAfter "_parser"

      elabCommand <| ← if let some lhsPrec := lhsPrec? then
        `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : TrailingParserDescr :=
            ParserDescr.trailingNode $(quote catName) $(quote leadPrec) $(quote lhsPrec) $val)
      else
        `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : ParserDescr :=
            ParserDescr.node $(quote catName) $(quote leadPrec) $val)

    -- Define variable parsers, plus variable category parser in symbol category.
    let varCatName := varCatOfName canon
    let varAttrIdent := mkIdent <| varAttrOfName canon
    for alias in aliases do
      let aliasName@(.str .anonymous nameStr) := alias.getId | throwUnsupportedSyntax
      let parserIdent := mkIdentFrom alias <| canonName ++ aliasName.appendAfter "_parser"
      elabCommand <| ←
        `(@[$varAttrIdent:ident] def $parserIdent : Parser :=
            leadingNode $(quote varCatName) Parser.maxPrec <|
              Lott.DSL.identPrefix $(quote nameStr))

    let varParserIdent := mkIdentFrom canon <| canonName.appendAfter "_variable_parser"
    elabCommand <| ←
      `(@[$attrIdent:ident] def $varParserIdent : ParserDescr :=
          ParserDescr.node $(quote catName) $(quote leadPrec) <|
            ParserDescr.cat $(quote varCatName) $(quote leadPrec))

    -- Define desugar macros.
    let catIdent := mkIdent catName
    for prod in prods do
      let `(Production| | $[$ps]* : $prodIdent (desugar := $rhsTerm)) := prod | continue
      let macroIdent := mkIdentFrom prodIdent <| canonName ++ prodIdent.getId |>.appendAfter "_macro"
      let patternArgs ← ps.mapM fun stx =>
        match stx with
        | `($name:ident) => do
          let cat := symbolPrefix ++ (← resolveSymbol name)
          `($name@(Lean.Syntax.node _ $(quote cat) _))
        | `(stx| $atom:str) => `(Lean.Syntax.atom _ $(mkStrLit atom.getString.trim))
        | _ => throwUnsupportedSyntax
      elabCommand <| ←
        `(@[macro $catIdent] def $macroIdent : Lean.Macro
            | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => $rhsTerm
            | _ => Lean.Macro.throwUnsupported)

    -- Define elaboration.
    let prodMatchAlts ← prods.filterMapM fun prod => do
      let `(Production| | $[$ps]* : $prodIdent $[$desugarConfig?]? $[$elabConfig?]?) := prod
        | throwUnsupportedSyntax
      if desugarConfig?.isSome then return none

      let (patternArgs, seqItems, exprArgs) ← ps.foldlM (init := (#[], #[], #[])) fun (pa, si, ea) stx =>
        match stx with
        | `($name:ident) => do
          let cat := quote <| symbolPrefix ++ (← resolveSymbol name)
          return (
            pa.push <| ← `($name@(Lean.Syntax.node _ $cat _)),
            si.push <| ← `(doSeqItem| let $name ← Lott.DSL.elabTerm $cat $name),
            ea.push name,
          )
        | `(stx| $atom:str) =>
          return (pa.push (← `(Lean.Syntax.atom _ $(mkStrLit atom.getString.trim))), si, ea)
        | _ => throwUnsupportedSyntax

      let rest ← if let some elabConfig := elabConfig? then
          let `(ElabConfig| (elab := $rest)) := elabConfig | throwUnsupportedSyntax
          pure rest
        else
          `(term| return Lean.mkAppN (Lean.Expr.const $(quote <| ns ++ canonName ++ prodIdent.getId) []) #[$exprArgs,*])

      `(matchAltExpr|
        | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
          $seqItems*
          $rest:term)

    let termElabIdent := mkIdentFrom canon <| canonName.appendAfter "TermElab"
    elabCommand <| ←
      `(@[lott_elab $catIdent] def $termElabIdent : Lott.DSL.LottElab
          $prodMatchAlts:matchAlt*
          | Lean.Syntax.node _ $(quote catName) #[Lean.Syntax.node _ $(quote varCatName) #[ident@(Lean.Syntax.ident ..)] ] => do
            let type ← Lean.Elab.Term.elabType <| mkIdent $(quote <| ns ++ canonName)
            Lean.Elab.Term.elabTerm ident type
          | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

elab_rules : command
  | `($nt:Lott.DSL.NonTerminal) => elabNonTerminals #[nt]
  | `(mutual $[$nts:Lott.DSL.NonTerminal]* end) => elabNonTerminals nts

/- Subrule syntax. -/

elab_rules : command | `(subrule $names,* of $parent := $prods,*) => do
  let names := names.getElems.toList
  let canon :: aliases := names | throwUnsupportedSyntax
  let canonName := canon.getId
  let ns ← getCurrNamespace
  let canonQualified := ns ++ canonName

  -- Declare syntax category.
  let catName := symbolPrefix ++ ns ++ canonName
  let attrName := catName.appendAfter "_parser"
  setEnv <| ← Parser.registerParserCategory (← getEnv) attrName catName .symbol

  for name in names do
    setEnv <| lottSymbolAliasExt.addEntry (← getEnv)
      { canon := canonQualified, alias := ns ++ name.getId }

  -- Declare parsers in category.
  let attrIdent := mkIdent attrName
  for alias in aliases do
    let aliasName@(.str .anonymous nameStr) := alias.getId | throwUnsupportedSyntax
    let parserIdent := mkIdentFrom alias <| canonName ++ aliasName.appendAfter "_parser"
    elabCommand <| ←
      `(@[$attrIdent:ident] def $parserIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <|
            Lott.DSL.identPrefix $(quote nameStr))

  -- TODO: Support parsing of the subset of the syntax instead of just variables.

  let parentName ← resolveSymbol parent
  let parentCatName := symbolPrefix ++ parentName
  let parentAttrIdent := mkIdent <| parentCatName.appendAfter "_parser"
  let parentParserIdent := mkIdentFrom canon <| parentName ++ canonName.appendAfter "_parser"
  elabCommand <| ←
    `(@[$parentAttrIdent:ident] def $parentParserIdent : ParserDescr :=
        ParserDescr.node $(quote parentCatName) $(quote leadPrec) <|
          ParserDescr.cat $(quote catName) 0)

  -- Declare type.
  let matchAlts ← prods.getElems.mapM fun prod =>
    `(matchAltExpr| | $(mkIdentFrom prod <| (parentName ++ prod.getId)) .. => True)
  elabCommand <| ←
    `(def $canon := { x : $parent // match x with $matchAlts:matchAlt* | _ => False })

  -- Define elaboration.
  let catIdent := mkIdentFrom canon catName
  let termElabName := mkIdentFrom canon <| canon.getId.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_elab $catIdent] def $termElabName : Lott.DSL.LottElab
        | Lean.Syntax.node _ $(quote catName) #[ident@(Lean.Syntax.ident ..)] => do
          let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
          Lean.Elab.Term.elabTerm ident type
        | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

  -- Define parent elaboration.
  let parentCatIdent := mkIdent parentCatName
  let parentTermElabName := mkIdent <| parentName.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_elab $parentCatIdent] def $parentTermElabName : Lott.DSL.LottElab
        | Lean.Syntax.node _ $(quote parentCatName) #[Lean.Syntax.node _ $(quote catName) #[ident@(Lean.Syntax.ident ..)] ] => do
          let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
          let e ← Lean.Elab.Term.elabTerm ident type
          return Lean.Expr.proj `Subtype 0 e
        | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

/- Judgement syntax. -/

elab_rules : command | `(judgement_syntax $ps* : $name) => do
  -- Declare syntax category.
  let ns ← getCurrNamespace
  let catName := judgementPrefix ++ ns ++ name.getId
  let attrName := catName.appendAfter "_parser"
  setEnv <| ← Parser.registerParserCategory (← getEnv) attrName catName .symbol

  -- Declare parser.
  let ps := ps.map (β := TSyntax [`Lean.Parser.Syntax.atom, `ident]) fun
    | `($name:ident) => name
    | `(atom| $atom) => atom
  let syntaxParser := mkNullNode <| ← ps.mapM (β := Syntax) fun
    | `($name:ident) => do
      `(cat| $(mkIdentFrom name <| symbolPrefix ++ (← resolveSymbol name)):ident)
    | other => return other
  let (val, none) ← liftTermElabM <| toParserDescr syntaxParser catName
    | throwError "invalid left recursive judgement syntax"
  let parserIdent := mkIdentFrom name <| name.getId.appendAfter "_parser"
  elabCommand <| ←
    `(@[Lott.Judgement_parser, $(mkIdentFrom name attrName):ident] def $parserIdent : ParserDescr :=
      ParserDescr.node $(quote catName) $(quote leadPrec) $val)

  -- Define elaboration.
  let (patternArgs, seqItems, exprArgs) ← ps.foldlM (init := (#[], #[], #[])) fun (pa, si, ea) stx =>
    match stx with
    | `($name:ident) => do
      let cat := quote <| symbolPrefix ++ (← resolveSymbol name)
      return (
        pa.push <| ← `($name@(Lean.Syntax.node _ $cat _)),
        si.push <| ← `(doSeqItem| let $name ← Lott.DSL.elabTerm $cat $name),
        ea.push name,
      )
    | `(stx| $atom:str) =>
      return (pa.push (← `(Lean.Syntax.atom _ $(mkStrLit atom.getString.trim))), si, ea)
    | _ => throwUnsupportedSyntax
  let catIdent := mkIdentFrom name catName
  let termElabIdent := mkIdentFrom name <| name.getId.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_elab $catIdent] def $termElabIdent : Lott.DSL.LottElab
        | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
          $seqItems*
          let name := $(quote <| ns ++ name.getId)
          let some e ← Lean.Elab.Term.resolveId? <| Lean.mkIdent name
            | Lean.throwError s!"failed to resolve judgement identifier {name} (potential use of judgement embedding before judgement declaration)"
          return Lean.mkAppN e #[$exprArgs,*]
        | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

  setEnv <| lottJudgementSyntaxExt.modifyState (← getEnv)
    fun ({ byName }) => { byName := byName.insert (ns ++ name.getId) ps }

private
def elabJudgementDecls (jds : Array Syntax) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let inductives ← jds.mapM fun jd => do
    let `(JudgementDecl| judgement $name := $rules*) := jd | throwUnsupportedSyntax

    let state := lottJudgementSyntaxExt.getState (← getEnv)
    let catName := ns ++ name.getId
    let .some ps := state.byName.find? catName
      | throwError "judgement_syntax for {name} not given before use in judgement"

    let type ← ps.reverse.foldlM (init := ← `(term| Prop)) fun
      | acc, `($name:ident) => do `($(mkIdentFrom name (← resolveSymbol name)) → $acc)
      | acc, _ => return acc

    let ctors ← rules.mapM fun rule => do
      let `(InferenceRule| $jms:Lott.Judgement* $[─]* $ruleIdent $conclusion:Lott.Judgement) := rule
        | throwUnsupportedSyntax
      let conclusionKind := conclusion.raw.getKind 
      let expectedKind := judgementPrefix ++ catName
      if conclusionKind != expectedKind then
        throwErrorAt conclusion "found conclusion judgement syntax kind{indentD conclusionKind}\nexpected to find kind{indentD expectedKind}\nall conclusions of inference rules in a judgement declaration must be the judgement which is being defined"
      let ctorType ← jms.foldrM (init := ← `(term| [[$conclusion:Lott.Judgement]]))
        fun «judgement» acc => `([[$«judgement»:Lott.Judgement]] → $acc)
      `(ctor| | $ruleIdent:ident : $ctorType)
    `(inductive $name : $type where $ctors*)
  elabCommand <| ← `(mutual $inductives* end)

elab_rules : command
  | `($jd:Lott.DSL.JudgementDecl) => elabJudgementDecls #[jd]
  | `(mutual $[$jds:Lott.DSL.JudgementDecl]* end) => elabJudgementDecls jds

end Lott.DSL
