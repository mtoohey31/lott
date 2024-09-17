import Lott.DSL.Environment
import Lott.DSL.Parser
import Lott.DSL.IR

-- TODO: Remove unnecessary qualifications from names.
-- TODO: Delab to embeddings when possible.

namespace Lott.DSL

open Lean
open Lean.Data
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Syntax
open Lean.Parser
open Lean.Parser.Command
open Lean.Parser.Syntax
open Lean.Parser.Term

/- Term embedding syntax. -/

abbrev TermElab := Syntax → TermElabM Expr

private unsafe
def mkLottTermElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute TermElab) := do
  mkElabAttribute TermElab .anonymous `lott_term_elab `Lott `Lott.DSL.TermElab "lott" ref

@[implemented_by mkLottTermElabAttributeUnsafe]
opaque mkLottTermElabAttribute (ref : Name) : IO (KeyedDeclsAttribute TermElab)

initialize lottTermElabAttribute : KeyedDeclsAttribute TermElab ← mkLottTermElabAttribute decl_name%

partial
def elabTerm (catName : Name) : TermElab := fun stx => do
  let result ← liftMacroM <| expandMacroImpl? (← getEnv) stx
  match result with
  | some (decl, stxNew?) => do
    let stxNew ← liftMacroM <| liftExcept stxNew?
    withInfoContext' stx (mkInfo := mkTermInfo decl stx) <|
      withMacroExpansion stx stxNew <|
        withRef stxNew <|
          elabTerm catName stxNew
  | none => match lottTermElabAttribute.getEntries (← getEnv) catName with
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
          if id == unsupportedSyntaxExceptionId then elabTermWithFns stx elabFns else throw ex
        | _ => throw ex

@[term_elab lott_symbol_embed]
private
def symbolEmbedElab : Term.TermElab := fun stx _ => do
  let stx := stx[3]!
  elabTerm stx.getKind stx

elab_rules : term
  | `([[$stx:Lott.Symbol]]) => elabTerm stx.raw.getKind stx
  | `([[$stx:Lott.Judgement]]) => elabTerm stx.raw.getKind stx

abbrev TexElab := (ref : Syntax) → Syntax → TermElabM String

private unsafe
def mkLottTexElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute TexElab) := do
  mkElabAttribute TexElab .anonymous `lott_tex_elab `Lott `Lott.DSL.TexElab "lott" ref

@[implemented_by mkLottTexElabAttributeUnsafe]
opaque mkLottTexElabAttribute (ref : Name) : IO (KeyedDeclsAttribute TexElab)

initialize lottTexElabAttribute : KeyedDeclsAttribute TexElab ← mkLottTexElabAttribute decl_name%

def elabTex (catName : Name) : TexElab := fun ref stx => do
  match lottTexElabAttribute.getEntries (← getEnv) catName with
  | [] =>
    throwErrorAt ref "tex elaboration function for '{catName}' has not been implemented{indentD stx}"
  | elabFns => elabTexWithFns ref stx elabFns
where
  elabTexWithFns ref stx
    | [] => unreachable!
    | [elabFn] => elabFn.value ref stx
    | elabFn :: elabFns => do
      try
        elabFn.value ref stx
      catch ex => match ex with
        | .internal id _ =>
          if id == unsupportedSyntaxExceptionId then elabTexWithFns ref stx elabFns else throw ex
        | _ => throw ex

/- Utility stuff. -/

private partial
def _root_.Lean.Data.Trie.findCommonPrefix (t : Trie α) (s : String) : Array α :=
  go t 0
where
  go (t : Trie α) (i : Nat) : Array α :=
    if h : i < s.utf8ByteSize then
      let c := s.getUtf8Byte i h
      match t with
      | .leaf (some val) => if i != 0 then #[val] else .empty
      | .leaf none => .empty
      | .node1 _ c' t' =>
        if c == c' then
          go t' (i + 1)
        else if i != 0 then
          t.values
        else
          .empty
      | .node _ cs ts =>
        match cs.findIdx? (· == c) with
        | none => if i != 0 then t.values else .empty
        | some idx => go (ts.get! idx) (i + 1)
    else
      t.values

def resolveSymbol (symbolName : Ident) (allowSuffix := true) : CommandElabM Name := do
  let name := symbolName.getId
  let state := symbolExt.getState (← getEnv)

  let find s := if allowSuffix then
      state.byAlias.findCommonPrefix s
    else
      state.byAlias.find? s |>.toArray

  -- First check if the name itself is present in the state.
  match find name.toString with
    -- If not, check if it's present when prepending the current namespace.
  | #[] => match find <| (← getCurrNamespace) ++ name |>.toString with
    -- Otherwise, check the namespaces we've opened.
    | #[] => do
      let names ← resolveOpensNames name state #[] (← getOpenDecls)
      let aliases := names.map find |>.flatten
      match aliases.foldl (fun acc a => acc.insert a.canon a) (mkNameMap _) |>.toList with
      | [] => throwErrorAt symbolName "unknown lott symbol {symbolName}"
      | [(canon, _)] => pure canon
      | results => disambiguate <| results.toArray.map Prod.snd
    | #[{ canon, .. }] => pure canon
    | results => disambiguate results
  | #[{ canon, .. }] => pure canon
  | results => disambiguate results
where
  resolveOpensNames name state acc
    | [] => pure #[]
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

  disambiguate results := do
    let sortedResults := results.qsort (·.alias.toString.length < ·.alias.toString.length)
    match sortedResults.filter (·.alias.toString.length == sortedResults[0]!.alias.toString.length) with
    | #[] => unreachable!
    | #[{ canon, .. }] => pure canon
    | results => throwErrorAt symbolName
        "ambiguous lott symbol {symbolName}; found multiple matches: {results.map (·.alias)}"

def texEscape (s : String) : String :=
  String.join <| s.data.map fun c => match c with
    | '&' | '%' | '$' | '#' | '_' | '{' | '}' => "\\" ++ c.toString
    | '~' => "\textasciitilde"
    | '^' => "\textasciicircum"
    | '\\' => "\textbackslash"
    | _ => c.toString

private
def variablePrefix := `Lott.Variable

private
def judgementPrefix := `Lott.Judgement

partial
def IR.ofStx : TSyntax `stx → CommandElabM IR
  | `(Lean.Parser.Command.elabArg| $l:ident:$stx:stx) => do
    let mk _ t ← IR.ofStx stx
    return mk l t
  | `(stx| $name:ident) => return mk name <| .category (← resolveSymbol name)
  | ref@`(stx| $s:str) => return mk (← mkFreshIdent ref) <| .atom s.getString
  | ref@`(stx| sepBy($[$ps]*, $sep)) =>
    return mk (← mkFreshIdent ref) <| .sepBy (← ps.mapM IR.ofStx) sep.getString
  | ref@`(stx| optional($[$ps]*)) =>
    return mk (← mkFreshIdent ref) <| .optional <| ← ps.mapM IR.ofStx
  | _ => throwUnsupportedSyntax

private
def mkMkProd (entries : Array (Term × Term)) : CommandElabM (Option (Term × Term)) := do
  let some back := entries.back? | return none
  let res ← entries.extract 0 (entries.size - 1) |>.foldrM (init := back)
    fun (expr, type) (mkProdAcc, typeAcc) =>
    return (
      ← ``(mkApp4 (Expr.const `Prod.mk [levelOne, levelOne]) $type $typeAcc $expr $mkProdAcc),
      ← ``(mkApp2 (Expr.const `Prod [levelOne, levelOne]) $type $typeAcc)
    )
  return some res

private partial
def IR.toExprArgs (ir : Array IR) : CommandElabM (TSepArray `term ",") :=
  ir.filterMapM (β := TSyntax `term) fun | ir@(mk l _) => do
      if (← IR.toType ir).isNone then
        return none

      return some l

private partial
def IR.toTermSeqItems (ir : Array IR) : CommandElabM (TSyntaxArray `Lean.Parser.Term.doSeqItem) :=
  ir.filterMapM fun
    | mk l (.category n) => `(doSeqItem| let $l ← Lott.DSL.elabTerm $(quote <| symbolPrefix ++ n) $l)
    | mk _ (.atom _) => return none
    | mk l (.sepBy ir _) => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTermSeqItems ir
      let exprArgs ← IR.toExprArgs ir
      let exprTypes ← ir.filterMapM IR.toMkTypeExpr
      let some (mkProd, type) ← mkMkProd (exprArgs.getElems.zip exprTypes) | return none

      `(doSeqItem| let $l ← do
          let prodExprs ← Syntax.getArgs $l |>.mapM fun stx => do
            let Syntax.node _ _ #[$patternArgs,*] := stx | throwUnsupportedSyntax
            $seqItems*
            return $mkProd
          Meta.liftMetaM <| Meta.mkArrayLit $type prodExprs.toList)
    | mk l (.optional ir) => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTermSeqItems ir
      let exprArgs ← IR.toExprArgs ir
      let exprTypes ← ir.filterMapM IR.toMkTypeExpr
      let some (mkProd, type) ← mkMkProd (exprArgs.getElems.zip exprTypes) | return none

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx => do
            let Syntax.node _ _ #[$patternArgs,*] := stx | throwUnsupportedSyntax
            $seqItems*
            return mkApp2 (Expr.const `Option.some [levelOne]) $type $mkProd
          | none => return mkApp (Expr.const `Option.none [levelOne]))

partial
def IR.toTexSeqItems (ir : Array IR) : CommandElabM (TSyntaxArray `Lean.Parser.Term.doSeqItem) :=
  ir.mapM fun
    | mk l (.category n) => `(doSeqItem| let $l ← Lott.DSL.elabTex $(quote <| symbolPrefix ++ n) ref $l)
    | mk l (.atom s) => `(doSeqItem| let $l := $(quote s))
    | mk l (.sepBy ir _) => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir
      let joinArgs := IR.toJoinArgs ir

      `(doSeqItem| let $l ← do
          let strings ← Syntax.getArgs $l |>.mapM fun stx => do
            let Syntax.node _ _ #[$patternArgs,*] := stx | throwUnsupportedSyntax
            $seqItems*
            return String.join [$joinArgs,*]
          pure <| String.join strings.toList)
    | mk l (.optional ir) => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir
      let joinArgs := IR.toJoinArgs ir

      `(doSeqItem| let $l ← (Syntax.getArgs $l)[0]?.mapM fun stx => do
          let Syntax.node _ _ #[$patternArgs,*] := stx | throwUnsupportedSyntax
          $seqItems*
          return String.join [$joinArgs,*])

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
    setEnv <| symbolExt.addEntry (← getEnv) { canon := canonQualified, alias := ns ++ name.getId }
  elabCommand <| ← `(instance (x y : $canon) : Decidable (x = y) := Nat.decEq x y)

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
      `(@[$(mkIdent parserAttrName):ident] def $parserIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <| Lott.DSL.identPrefix $(quote nameStr))

  -- Define elaboration.
  let catIdent := mkIdent catName
  let termElabName := mkIdentFrom canon <| canon.getId.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_term_elab $catIdent] def $termElabName : Lott.DSL.TermElab
        | Lean.Syntax.node _ $(quote catName) #[ident@(Lean.Syntax.ident ..)] => do
          let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
          Lean.Elab.Term.elabTerm ident type
        | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)
  let texElabName := mkIdentFrom canon <| canon.getId.appendAfter "TexElab"
  elabCommand <| ←
    `(@[lott_tex_elab $catIdent] def $texElabName : Lott.DSL.TexElab
        | _, Lean.Syntax.node _ $(quote catName) #[Lean.Syntax.ident _ _ n _] => do
          return Lott.DSL.texEscape <| n.toString (escape := false)
        | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

/- Non-terminal syntax. -/

private
inductive ProductionType where
  | none
  | sugar (desugar' : Term)
  | customElab (elab' : Term)
deriving BEq

private
structure Production where
  name : Ident
  ir : Array IR
  type : ProductionType

private
structure NonTerminal where
  canon : Ident
  aliases : Array Ident
  prods : Array Production

private
def NonTerminal.catName (nt : NonTerminal) : CommandElabM Name :=
  return symbolPrefix ++ (← getCurrNamespace) ++ nt.canon.getId

private
def NonTerminal.varCatName (nt : NonTerminal) : CommandElabM Name :=
  return variablePrefix ++ (← getCurrNamespace) ++ nt.canon.getId

private
def NonTerminal.parserAttrName (nt : NonTerminal) : CommandElabM Name :=
  return (← nt.catName).appendAfter "_parser"

private
def NonTerminal.varParserAttrName (nt : NonTerminal) : CommandElabM Name :=
  return (← nt.varCatName).appendAfter "_parser"

private
def elabNonTerminals (nts : Array Syntax) : CommandElabM Unit := do
  -- Populate alias map immediately so we can resolve stuff within the current mutual throughout the
  -- following steps.
  let ns ← getCurrNamespace
  for nt in nts do
    let `(NonTerminal| nonterminal $[$names],* := $_*) := nt | throwUnsupportedSyntax
    let names@(canonName :: _) := names.toList | throwUnsupportedSyntax
    for name in names do
      setEnv <| symbolExt.addEntry (← getEnv)
        { canon := ns ++ canonName.getId, alias := ns ++ name.getId }

  -- Transform syntax into non-terminal structure.
  let nts ← nts.mapM fun nt => do
    let `(NonTerminal| nonterminal $[$names],* := $prods*) := nt | throwUnsupportedSyntax
    let some canon := names[0]? | throwUnsupportedSyntax
    let aliases := names.extract 1 names.size

    let prods ← prods.mapM fun prod => do
      let `(Production| | $[$ps]* : $name $[(desugar := $desugar?)]? $[(elab := $elab?)]?) := prod
        | throwUnsupportedSyntax

      let ir ← ps.mapM IR.ofStx

      let type ← match desugar?, elab? with
      | some _, some _ => throwUnsupportedSyntax
      | some desugar', none => pure <| .sugar desugar'
      | none, some elab' => pure <| .customElab elab'
      | none, none => pure .none

      return { name, ir, type }

    return { canon, aliases, prods : NonTerminal }

  -- Define mutual inductives and parser categories.
  let inductives ← nts.mapM fun nt@{ canon, prods, .. } => do
    setEnv <| ← registerParserCategory (← getEnv) (← nt.parserAttrName) (← nt.catName) .symbol
    setEnv <| ← registerParserCategory (← getEnv) (← nt.varParserAttrName) (← nt.varCatName) .symbol

    let ctors ← prods.filterMapM fun { name, ir, type } => do
      if type != .none then return none
      let ctorType ← IR.toTypeArrSeq ir canon
      `(ctor| | $name:ident : $ctorType)
    `(inductive $canon where $ctors*)
  if let ⟨[i]⟩ := inductives then
    elabCommand i.raw
  else
    elabCommand <| ← `(mutual $inductives* end)

  for nt@{ canon, aliases, prods, .. } in nts do
    -- Define production parsers.
    let canonName := canon.getId
    let attrIdent := mkIdent <| ← nt.parserAttrName
    for { name, ir, .. } in prods do
      let (val, type) ← IR.toParser ir <| ← nt.catName
      let parserIdent := mkIdentFrom name <| canonName ++ name.getId |>.appendAfter "_parser"
      elabCommand <| ← `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : $type := $val)

    -- Define variable parsers, plus variable category parser in symbol category.
    let varAttrIdent := mkIdent <| ← nt.varParserAttrName
    for alias in aliases do
      let aliasName@(.str .anonymous nameStr) := alias.getId | throwUnsupportedSyntax
      let parserIdent := mkIdentFrom alias <| canonName ++ aliasName.appendAfter "_parser"
      elabCommand <| ←
        `(@[$varAttrIdent:ident] def $parserIdent : Parser :=
            leadingNode $(quote <| ← nt.varCatName) Parser.maxPrec <|
              Lott.DSL.identPrefix $(quote nameStr))

    let varParserIdent := mkIdentFrom canon <| canonName.appendAfter "_variable_parser"
    elabCommand <| ←
      `(@[$attrIdent:ident] def $varParserIdent : Parser :=
          leadingNode $(quote <| ← nt.catName) Parser.maxPrec <|
            categoryParser $(quote <| ← nt.varCatName) Parser.maxPrec)

    -- Define desugar macros and elaboration.
    let catIdent := mkIdent <| ← nt.catName
    let termProdMatchAlts ← prods.filterMapM fun { name, ir, type } => do
      let patternArgs ← IR.toPatternArgs ir

      if let .sugar desugar' := type then
        let macroIdent := mkIdentFrom name <| canonName ++ name.getId |>.appendAfter "_macro"
        elabCommand <| ←
          `(@[macro $catIdent] def $macroIdent : Lean.Macro
              | Lean.Syntax.node _ $(quote <| ← nt.catName) #[$patternArgs,*] => $desugar'
              | _ => Lean.Macro.throwUnsupported)
        return none

      let seqItems ← IR.toTermSeqItems ir
      let exprArgs ← IR.toExprArgs ir
      let rest ← if let .customElab elab' := type then
          pure elab'
        else
          `(term| return Lean.mkAppN (Lean.Expr.const $(quote <| ns ++ canonName ++ name.getId) [])
                    #[$exprArgs,*])

      `(matchAltExpr|
        | Lean.Syntax.node _ $(quote <| ← nt.catName) #[$patternArgs,*] => do
          $seqItems*
          $rest:term)

    let termElabIdent := mkIdentFrom canon <| canonName.appendAfter "TermElab"
    elabCommand <| ←
      `(@[lott_term_elab $catIdent] def $termElabIdent : Lott.DSL.TermElab
          $termProdMatchAlts:matchAlt*
          | Lean.Syntax.node _ $(quote <| ← nt.catName) #[
              Lean.Syntax.node _ $(quote <| ← nt.varCatName) #[ident@(Lean.Syntax.ident ..)]
            ] => do
            let type ← Lean.Elab.Term.elabType <| mkIdent $(quote <| ns ++ canonName)
            Lean.Elab.Term.elabTerm ident type
          | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

    let texProdMatchAlts ← prods.mapM fun { ir, .. } => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir
      let joinArgs := IR.toJoinArgs ir

      `(matchAltExpr| | ref, Lean.Syntax.node _ $(quote <| ← nt.catName) #[$patternArgs,*] => do
          $seqItems*
          return String.join [$joinArgs,*])

    let texElabName := mkIdentFrom canon <| canon.getId.appendAfter "TexElab"
    elabCommand <| ←
      `(@[lott_tex_elab $catIdent] def $texElabName : Lott.DSL.TexElab
          $texProdMatchAlts:matchAlt*
          | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
              Lean.Syntax.node _ $(quote <| ← nt.varCatName) #[Lean.Syntax.ident _ _ n _]
            ] => return Lott.DSL.texEscape <| n.toString (escape := false)
          | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

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
  let parserAttrName := catName.appendAfter "_parser"
  setEnv <| ← Parser.registerParserCategory (← getEnv) parserAttrName catName .symbol

  for name in names do
    setEnv <| symbolExt.addEntry (← getEnv)
      { canon := canonQualified, alias := ns ++ name.getId }

  -- Declare parsers in category.
  for alias in aliases do
    let aliasName@(.str .anonymous nameStr) := alias.getId | throwUnsupportedSyntax
    let parserIdent := mkIdentFrom alias <| canonName ++ aliasName.appendAfter "_parser"
    elabCommand <| ←
      `(@[$(mkIdent parserAttrName):ident] def $parserIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <|
            Lott.DSL.identPrefix $(quote nameStr))

  -- TODO: Support parsing of the subset of the syntax instead of just variables.

  let parentName ← resolveSymbol parent (allowSuffix := false)
  let parentCatName := symbolPrefix ++ parentName
  let parentParserAttrIdent := mkIdent <| parentCatName.appendAfter "_parser"
  let parentParserIdent := mkIdentFrom canon <| parentName ++ canonName.appendAfter "_parser"
  elabCommand <| ←
    `(@[$parentParserAttrIdent:ident] def $parentParserIdent : Parser :=
        leadingNode $(quote parentCatName) Parser.maxPrec <| categoryParser $(quote catName) 0)

  -- Declare type.
  let matchAlts ← prods.getElems.mapM fun prod =>
    `(matchAltExpr| | $(mkIdentFrom prod <| (parentName ++ prod.getId)) .. => True)
  elabCommand <| ← `(def $canon := { x : $parent // match x with $matchAlts:matchAlt* | _ => False })

  -- Define elaboration.
  let termElabName := mkIdentFrom canon <| canon.getId.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_term_elab $(mkIdent catName)] def $termElabName : Lott.DSL.TermElab
        | Lean.Syntax.node _ $(quote catName) #[ident@(Lean.Syntax.ident ..)] => do
          let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
          Lean.Elab.Term.elabTerm ident type
        | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

  -- Define parent elaboration.
  let parentCatIdent := mkIdent parentCatName
  let parentTermElabName := mkIdent <| parentName.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_term_elab $parentCatIdent] def $parentTermElabName : Lott.DSL.TermElab
        | Lean.Syntax.node _ $(quote parentCatName) #[
            Lean.Syntax.node _ $(quote catName) #[ident@(Lean.Syntax.ident ..)]
          ] => do
          let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
          let e ← Lean.Elab.Term.elabTerm ident type
          return Lean.Expr.proj `Subtype 0 e
        | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

  let parentTexElabName := mkIdent <| parentName.appendAfter "TexElab"
  elabCommand <| ←
    `(@[lott_tex_elab $parentCatIdent] def $parentTexElabName : Lott.DSL.TexElab
        | _, Lean.Syntax.node _ $(quote parentCatName) #[
            Lean.Syntax.node _ $(quote catName) #[Lean.Syntax.ident _ _ n _]
          ] => return Lott.DSL.texEscape <| n.toString (escape := false)
        | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

/- Judgement syntax. -/

elab_rules : command | `(judgement_syntax $[$ps]* : $name) => do
  -- Declare syntax category.
  let ns ← getCurrNamespace
  let qualified := ns ++ name.getId
  let catName := judgementPrefix ++ qualified
  let parserAttrName := catName.appendAfter "_parser"
  setEnv <| ← Parser.registerParserCategory (← getEnv) parserAttrName catName .symbol

  -- Add to environment extension.
  let ir ← ps.mapM IR.ofStx
  setEnv <| judgementExt.addEntry (← getEnv) { name := qualified, ir }

  -- Declare parser.
  let (val, type) ← IR.toParser ir catName
  if type != (← `(term| Parser)) then throwError "invalid left recursive judgement syntax"
  let parserIdent := mkIdentFrom name <| name.getId.appendAfter "_parser"
  elabCommand <| ←
    `(@[Lott.Judgement_parser, $(mkIdent parserAttrName):ident] def $parserIdent : Parser := $val)

  -- Define elaboration.
  let patternArgs ← IR.toPatternArgs ir
  let termSeqItems ← IR.toTermSeqItems ir
  let exprArgs ← IR.toExprArgs ir
  let catIdent := mkIdent catName
  let termElabIdent := mkIdentFrom name <| name.getId.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_term_elab $catIdent] def $termElabIdent : Lott.DSL.TermElab
        | Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
          $termSeqItems*
          let name := $(quote qualified)
          let some e ← Lean.Elab.Term.resolveId? <| Lean.mkIdent name
            | Lean.throwError s!"failed to resolve judgement identifier {name} (potential use of judgement embedding before judgement declaration)"
          return Lean.mkAppN e #[$exprArgs,*]
        | _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

  let texSeqItems ← IR.toTexSeqItems ir
  let joinArgs := IR.toJoinArgs ir
  let texElabName := mkIdentFrom name <| name.getId.appendAfter "TexElab"
  elabCommand <| ←
    `(@[lott_tex_elab $catIdent] def $texElabName : Lott.DSL.TexElab
        | ref, Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
          $texSeqItems*
          return String.join [$joinArgs,*]
        | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

private
def elabJudgementDecls (jds : Array Syntax) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let inductives ← jds.mapM fun jd => do
    let `(JudgementDecl| judgement $name := $rules*) := jd | throwUnsupportedSyntax

    let catName := ns ++ name.getId
    let .some { ir, .. } := judgementExt.getState (← getEnv) |>.byName.find? catName
      | throwError "judgement_syntax for {name} not given before use in judgement"

    let type ← IR.toTypeArrSeq ir <| ← `(term| Prop)
    let ctors ← rules.mapM fun rule => do
      let `(InferenceRule| $jms:Lott.Judgement* $[─]* $name $conclusion:Lott.Judgement) := rule
        | throwUnsupportedSyntax
      let conclusionKind := conclusion.raw.getKind
      let expectedKind := judgementPrefix ++ catName
      if conclusionKind != expectedKind then
        throwErrorAt conclusion "found conclusion judgement syntax kind{indentD conclusionKind}\nexpected to find kind{indentD expectedKind}\nall conclusions of inference rules in a judgement declaration must be the judgement which is being defined"
      let ctorType ← jms.foldrM (init := ← `(term| [[$conclusion:Lott.Judgement]]))
        fun «judgement» acc => `([[$«judgement»:Lott.Judgement]] → $acc)
      `(ctor| | $name:ident : $ctorType)
    `(inductive $name : $type where $ctors*)
  if let ⟨[i]⟩ := inductives then
    elabCommand i.raw
  else
    elabCommand <| ← `(mutual $inductives* end)

elab_rules : command
  | `($jd:Lott.DSL.JudgementDecl) => elabJudgementDecls #[jd]
  | `(mutual $[$jds:Lott.DSL.JudgementDecl]* end) => elabJudgementDecls jds

/- External interaction syntax. -/

open IO.FS in
elab_rules : command
  | `(filter $inputFname:str $outputFname:str) => do
    let input ← readFile inputFname.getString

    let s := mkParserState input
    let ictx := mkInputContext input inputFname.getString
    let env ← getEnv
    let s := filterParser.fn.run ictx { env, options := {} } (getTokenTable env) s
    if !s.allErrors.isEmpty then
      throwError s.toErrorMsg ictx
    else if !ictx.input.atEnd s.pos then
      throwError s.mkError "end of input" |>.toErrorMsg ictx

    let output ← s.stxStack.toSubarray.toArray.mapM fun
      | .node _ `Lott.NonEmbed #[.atom _ s] => return s
      | stx => do
        let s ← liftTermElabM <| elabTex stx.getKind inputFname stx
        return "$" ++ s ++ "$"

    liftIO <| writeFile outputFname.getString <| String.join output.toList

end Lott.DSL
