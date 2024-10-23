import Lott.DSL.Environment
import Lott.DSL.Parser
import Lott.DSL.IR

-- TODO: Remove unnecessary qualifications from names.
-- TODO: Delab to embeddings when possible.

namespace Lott.DSL.Elab

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
open Lott.DSL.IR

/- Term embedding syntax. -/

abbrev TermElab := Bool → Syntax → TermElabM Expr

private unsafe
def mkLottTermElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute TermElab) := do
  mkElabAttribute TermElab .anonymous `lott_term_elab `Lott `Lott.DSL.Elab.TermElab "lott" ref

@[implemented_by mkLottTermElabAttributeUnsafe]
opaque mkLottTermElabAttribute (ref : Name) : IO (KeyedDeclsAttribute TermElab)

initialize lottTermElabAttribute : KeyedDeclsAttribute TermElab ← mkLottTermElabAttribute decl_name%

partial
def elabTerm (catName : Name) : TermElab := fun isBinder stx => do
  let result ← liftMacroM <| expandMacroImpl? (← getEnv) stx
  match result with
  | some (decl, stxNew?) => do
    let stxNew ← liftMacroM <| liftExcept stxNew?
    withInfoContext' stx (mkInfo := mkTermInfo decl stx) <|
      withMacroExpansion stx stxNew <|
        withRef stxNew <|
          elabTerm catName isBinder stxNew
  | none => match lottTermElabAttribute.getEntries (← getEnv) catName with
    | [] =>
      throwError "term elaboration function for '{catName}' has not been implemented{indentD stx}"
    | elabFns => elabTermWithFns isBinder stx elabFns
where
  elabTermWithFns isBinder stx
    | [] => unreachable!
    | [elabFn] => elabFn.value isBinder stx
    | elabFn :: elabFns => do
      try
        elabFn.value false stx
      catch ex => match ex with
        | .internal id _ =>
          if id == unsupportedSyntaxExceptionId then
            elabTermWithFns isBinder stx elabFns
          else
            throw ex
        | _ => throw ex

@[term_elab lott_symbol_embed]
private
def symbolEmbedElab : Term.TermElab := fun stx _ => do
  let stx := stx[3]!
  elabTerm stx.getKind false stx

elab_rules : term
  | `([[$stx:Lott.Symbol]]) => elabTerm stx.raw.getKind false stx
  | `([[$stx:Lott.Judgement]]) => elabTerm stx.raw.getKind false stx

abbrev TexElab := (ref : Syntax) → Syntax → TermElabM String

private unsafe
def mkLottTexElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute TexElab) := do
  mkElabAttribute TexElab .anonymous `lott_tex_elab `Lott `Lott.DSL.Elab.TexElab "lott" ref

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
  let state := aliasExt.getState (← getEnv)

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
def _root_.Lott.DSL.IR.ofStx : TSyntax `stx → CommandElabM IR
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
  let res ← entries.foldrM (start := entries.size - 1) (init := back)
    fun (expr, type) (mkProdAcc, typeAcc) =>
    return (
      ← ``(mkApp4 (Expr.const `Prod.mk [levelOne, levelOne]) $type $typeAcc $expr $mkProdAcc),
      ← ``(mkApp2 (Expr.const `Prod [levelOne, levelOne]) $type $typeAcc)
    )
  return some res

private partial
def _root_.Lott.DSL.IR.toExprArgs (ir : Array IR) (ids binders : Array Name)
  : CommandElabM (TSepArray `term ",") :=
  ir.filterMapM (β := Term) fun | ir@(mk l _) => do
      if (← IR.toType ids binders ir).isNone then
        return none

      return some l

private
def elabSymbolComprehension (symbol : TSyntax `Lott.Symbol) (i : Ident) (collection : Term)
  (type : Expr) : TermElabM Expr := do
  let stx ← `(Coe.coe (β := List Nat) $collection |>.map (fun $i => [[$symbol:Lott.Symbol]]) |>.join)
  Term.elabTerm stx (Expr.app (.const `List [levelOne]) type)

private partial
def _root_.Lott.DSL.IR.toTermSeqItems (ir : Array IR) (canon : Name) (ids binders : Array Name)
  : CommandElabM (TSyntaxArray `Lean.Parser.Term.doSeqItem) :=
  ir.filterMapM fun
    | mk l (.category n) => do
      if binders.contains l.getId then
        return none

      `(doSeqItem|
          let $l ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ n)
            $(quote <| ids.contains l.getId) $l)
    | mk _ (.atom _) => return none
    | mk l (.sepBy ir sep) => do
      let catName := sepByPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTermSeqItems ir canon ids binders
      let exprArgs ← IR.toExprArgs ir ids binders
      let exprTypes ← ir.filterMapM IR.toMkTypeExpr
      let some (mkProd, type) ← mkMkProd (exprArgs.getElems.zip exprTypes) | return none

      let termElabIdent := mkIdentFrom l <| canon ++ l.getId.appendAfter "TermElab"
      elabCommand <| ←
        `(@[lott_term_elab $(mkIdent catName)] def $termElabIdent : Lott.DSL.Elab.TermElab
            | _, Syntax.node _ $(quote catName) #[
              Lean.Syntax.atom _ "</",
              symbol,
              Lean.Syntax.atom _ "//",
              i@(Syntax.ident ..),
              Lean.Syntax.atom _ "∈",
              collection,
              Lean.Syntax.atom _ "/>"
            ] => do
              elabSymbolComprehension (TSyntax.mk symbol) (TSyntax.mk i) (TSyntax.mk collection) $type
            | _, Syntax.node _ $(quote catName) #[
                lhs@(Syntax.node _ $(quote catName) _),
                Lean.Syntax.atom _ $(quote sep.trim),
                rhs@(Syntax.node _ $(quote catName) _)
              ] => do
              let lhs ← Lott.DSL.Elab.elabTerm $(quote catName) false lhs
              let rhs ← Lott.DSL.Elab.elabTerm $(quote catName) false rhs
              Meta.liftMetaM <| Meta.reduce <| mkApp3 (Expr.const `List.append [0]) $type lhs rhs
            | _, Syntax.node _ $(quote catName) #[$patternArgs,*] => do
              $seqItems*
              return mkApp3 (Expr.const `List.cons [0]) $type $mkProd <| Expr.app (Expr.const `List.nil [0]) $type
            | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx => Lott.DSL.Elab.elabTerm $(quote catName) false stx
          | none => pure <| Expr.app (Expr.const `List.nil [0]) $type)
    | mk l (.optional ir) => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTermSeqItems ir canon ids binders
      let exprArgs ← IR.toExprArgs ir ids binders
      let exprTypes ← ir.filterMapM IR.toMkTypeExpr
      let some (mkProd, type) ← mkMkProd (exprArgs.getElems.zip exprTypes) | return none

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx => do
            let Syntax.node _ _ #[$patternArgs,*] := stx | throwUnsupportedSyntax
            $seqItems*
            return mkApp2 (Expr.const `Option.some [levelOne]) $type $mkProd
          | none => return Expr.app (Expr.const `Option.none [levelOne]))

partial
def _root_.Lott.DSL.IR.toTexSeqItems (ir : Array IR) (canon : Name) : CommandElabM (TSyntaxArray `Lean.Parser.Term.doSeqItem) :=
  ir.mapM fun
    | mk l (.category n) => `(doSeqItem| let $l ← Lott.DSL.Elab.elabTex $(quote <| symbolPrefix ++ n) ref $l)
    | mk l (.atom s) => `(doSeqItem| let $l := $(quote s))
    | mk l (.sepBy ir _) => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir canon
      let joinArgs := IR.toJoinArgs ir

      `(doSeqItem| let $l ← do
          let strings ← Syntax.getArgs $l |>.mapM fun stx => do
            let Syntax.node _ _ #[$patternArgs,*] := stx | throwUnsupportedSyntax
            $seqItems*
            return String.join [$joinArgs,*]
          pure <| String.join strings.toList)
    | mk l (.optional ir) => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir canon
      let joinArgs := IR.toJoinArgs ir

      `(doSeqItem| let $l ← (Syntax.getArgs $l)[0]?.mapM fun stx => do
          let Syntax.node _ _ #[$patternArgs,*] := stx | throwUnsupportedSyntax
          $seqItems*
          return String.join [$joinArgs,*])

partial
def toIsLocallyClosedCtor (prodIdent lcIdent : Ident) (qualified : Name) (ir : Array IR)
  (subst : Name × Name) (binders : Array Name) : CommandElabM (TSyntax `Lean.Parser.Command.ctor) :=
  do
  let (ctorTypeRetArgs, ctorTypeArgs) ← go ir
  let binders ← ctorTypeRetArgs.filterMapM fun
    | `(Lean.binderIdent| $_:hole) => return none
    | `(Lean.binderIdent| $i:ident) => `(bracketedBinder| {$i})
    | _ => throwUnsupportedSyntax
  let ctorType ← foldrArrow ctorTypeArgs <| ← ``($lcIdent ($(mkIdent <| qualified ++ prodIdent.getId) $(← toTerms ctorTypeRetArgs)*))
  return ← `(ctor| | $prodIdent:ident $binders:bracketedBinder* : $ctorType)
where
  toTerms (as : TSyntaxArray `Lean.binderIdent) : CommandElabM (Array Term) :=
    as.mapM fun
      | `(Lean.binderIdent| $h:hole) => `(term| $h:hole)
      | `(Lean.binderIdent| $i:ident) => `(term| $i:ident)
      | _ => throwUnsupportedSyntax

  go (ir : Array IR) (patAcc : TSyntaxArray `Lean.binderIdent := #[])
    (propAcc : Array Term := #[])
    : CommandElabM (TSyntaxArray `Lean.binderIdent × Array Term) := do
    let some (mk l irt) := ir[0]? | return (patAcc, propAcc)
    let ir' := ir.extract 1 ir.size

    if binders.contains l.getId then
        return ← go ir' patAcc propAcc

    let lbi ← `(Lean.binderIdent| $l:ident)
    let hole ← `(Lean.binderIdent| _)

    match irt with
    | .category n => do
      if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
        if substitutions.contains subst then
          go ir' (patAcc.push lbi) (propAcc.push <| ← `($(mkIdent <| n ++ subst.snd):ident $l))
        else
          go ir' patAcc propAcc
      else
        go ir' patAcc propAcc
    | .atom _ => go ir' patAcc propAcc
    | .sepBy ir _ => do
      match ← go ir with
      -- In this case, the sepBy doesn't actually contain anything stored in the datatype so we can
      -- just skip it.
      | (#[], #[]) => go ir' patAcc propAcc
      -- In this case, there is a list with stuff in it, but it doesn't contain anything for us to
      -- check, so we can just add an underscore pattern argument and proceed.
      | (_, #[]) => go ir' (patAcc.push hole) propAcc
      | (#[patArg], props) => go ir' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $patArg ∈ $l, $(← foldlAnd props))
      | (patArgs, props) => go ir' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $lbi ∈ $l, let $(← foldrProd <| ← toTerms patArgs):term := $l; $(← foldlAnd props))
    | .optional ir => do
      match ← go ir with
      -- In this case, the optional doesn't actually contain anything stored in the datatype so we can
      -- just skip it.
      | (#[], #[]) => go ir' patAcc propAcc
      -- In this case, there is a list with stuff in it, but it doesn't contain anything for us to
      -- check, so we can just add an underscore pattern argument and proceed.
      | (_, #[]) => go ir' (patAcc.push hole) propAcc
      | (#[patArg], props) => go ir' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $patArg:binderIdent ∈ $l, $(← foldlAnd props))
      | (patArgs, props) => go ir' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $lbi ∈ $l, let $(← foldrProd <| ← toTerms patArgs):term := $l; $(← foldlAnd props))

/- Metavariable syntax. -/

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
    elabCommand <| ← `(instance : SizeOf $canon := instSizeOf $canon)
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
          | .bound _, .free _ => isFalse (nomatch ·))
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
      `(@[$(mkIdent parserAttrName):ident] def $parserIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <| Lott.DSL.identPrefix $(quote nameStr))

  -- Define elaboration.
  let catIdent := mkIdent catName
  let termElabName := mkIdentFrom canon <| canon.getId.appendAfter "TermElab"
  let rhs ← if locallyNameless then
      `(do
          if isBinder then
              let type ← Lean.Elab.Term.elabType <| mkIdent $(quote <| canonQualified.appendAfter "Id")
              Lean.Elab.Term.elabTerm ident type
            else
              let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
              let expr ← Lean.Elab.Term.elabTerm (Syntax.mkCApp `Coe.coe #[.mk ident]) type
              Meta.liftMetaM <| Meta.reduce expr)
    else
      `(do
          let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
          Lean.Elab.Term.elabTerm ident type)
  elabCommand <| ←
    `(@[lott_term_elab $catIdent] def $termElabName : Lott.DSL.Elab.TermElab
        | isBinder, Lean.Syntax.node _ $(quote catName) #[ident@(Lean.Syntax.ident ..)] => $rhs
        | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)
  let texElabName := mkIdentFrom canon <| canon.getId.appendAfter "TexElab"
  elabCommand <| ←
    `(@[lott_tex_elab $catIdent] def $texElabName : Lott.DSL.Elab.TexElab
        | _, Lean.Syntax.node _ $(quote catName) #[Lean.Syntax.ident _ _ n _] => do
          return Lott.DSL.Elab.texEscape <| n.toString (escape := false)
        | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

/- Non-terminal syntax. -/

private
inductive ProductionType where
  | normal
  | sugar (desugar' : Term)
  | customElab (elab' : Term)
deriving BEq

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
  type : ProductionType
  bindConfig? : Option BindConfig
  ids : Array Name

private
def Production.binders (prod : Production) : Array Name :=
  prod.bindConfig?.toArray.map fun { of, .. } => of.getId

private
structure NonTerminal where
  canon : Ident
  aliases : Array Ident
  prods : Array Production
  parent? : Option Ident
  substitutions : Option (Array (Name × Name))

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
def elabNonTerminals (nts : Array Syntax) : CommandElabM Unit := do
  -- Populate alias map immediately so we can resolve stuff within the current mutual throughout the
  -- following steps.
  let ns ← getCurrNamespace
  for nt in nts do
    let `(NonTerminal| $[nosubst]? nonterminal $[(parent := $_)]? $[$names],* := $_*) := nt
      | throwUnsupportedSyntax
    let names@(canonName :: _) := names.toList | throwUnsupportedSyntax
    for name in names do
      setEnv <| aliasExt.addEntry (← getEnv)
        { canon := ns ++ canonName.getId, alias := ns ++ name.getId }

  -- Transform syntax into non-terminal structure.
  let nts ← nts.mapM fun nt => do
    let `(NonTerminal| $[nosubst%$ns]? nonterminal $[(parent := $parent?)]? $[$names],* := $prods*) := nt
      | throwUnsupportedSyntax
    let some canon := names[0]? | throwUnsupportedSyntax
    let aliases := names.extract 1 names.size

    let prodAndSubsts ← prods.mapM fun prod => do
      let `(Production| | $[$ps]* : $name $[$bindConfig?]? $[(id $ids?,*)]? $[(desugar := $desugar?)]? $[(elab := $elab?)]?) := prod
        | throwUnsupportedSyntax
      let ids := ids?.getD (.mk #[]) |>.getElems

      let ir ← ps.mapM IR.ofStx
      let subst ← match ir with
        | #[mk _ (.category n)] =>
          if metaVarExt.getState (← getEnv) |>.contains n then
            pure <| some n
          else
            pure none
        | _ => pure none

      let bindConfig? ← bindConfig?.mapM fun stx => do
        let `(BindConfig| (bind $of $[in $in',*]?)) := stx | throwUnsupportedSyntax
        let res := { of, in' := in'.getD (.mk #[]) : BindConfig }
        if let some x := ids.find? (res.find? ·.getId |>.isSome) then
          throwErrorAt x "name {x} also appears in bind config"
        for name in toStream res do
          if !containsName ir name.getId then
            logWarningAt name "name not found in syntax"
        return res

      let type ← match desugar?, elab? with
      | some _, some _ => throwUnsupportedSyntax
      | some desugar, none => pure <| .sugar desugar
      | none, some elab' => pure <| .customElab elab'
      | none, _ => pure <| .normal

      return ({ name, ir, type, bindConfig?, ids := ids.map TSyntax.getId }, subst)

    let (prods, substs) := prodAndSubsts.unzip
    let qualified := (← getCurrNamespace) ++ canon.getId
    let substitutions := if ns.isSome then none else substs.filterMap id |>.map ((·, qualified))

    let parent? ← parent?.mapM fun parent' =>
      return mkIdentFrom parent' <| ← resolveSymbol parent' (allowSuffix := false)

    return { canon, aliases, prods, parent?, substitutions : NonTerminal }

  -- Define mutual inductives and parser categories.
  let inductives ← nts.mapM fun nt@{ canon, prods, parent?, .. } => do
    setEnv <| ← registerParserCategory (← getEnv) (← nt.parserAttrName) (← nt.catName) .symbol
    setEnv <| ← registerParserCategory (← getEnv) (← nt.varParserAttrName) (← nt.varCatName) .symbol

    if let some parent' := parent? then
      if nts.size != 1 then
        throwErrorAt parent' "nonterminal with parent can't appear in a mutual block"

      let some { normalProds, .. } := symbolExt.getState (← getEnv) |>.find? parent'.getId
        | throwErrorAt parent' "unknown parent {parent'.getId}"

      let isIdent := mkIdentFrom canon <| parent'.getId ++ canon.getId.appendBefore "Is"
      let ctors ← prods.mapM fun prod@{ name, ir, type, .. } => match type with
        | .sugar ref | .customElab ref =>
          throwErrorAt ref "nonterminal with parent can only contain normal productions"
        | .normal => do
          let some pir := normalProds.find? name.getId
            | throwErrorAt name "normal production with matching name not found in parent"

          IR.toIsChildCtor name isIdent (← nt.qualified) parent'.getId ir pir prod.binders
      elabCommand <| ←
        `(inductive $(mkIdentFrom isIdent <| `_root_ ++ isIdent.getId) : $parent' → Prop where
            $ctors*)

      return ← `(def $canon := { x : $parent' // $isIdent x })

    let ctors ← prods.filterMapM fun prod@{ name, ir, type, ids, .. } => do
      let .normal := type | return none
      let ctorType ← IR.toTypeArrSeq ir canon ids prod.binders
      `(ctor| | $name:ident : $ctorType)
    `(inductive $canon where $ctors*)
  if let ⟨[i]⟩ := inductives then
    elabCommand i.raw
  else
    elabCommand <| ← `(mutual $inductives* end)

  let ntsMap ← nts.foldlM (init := mkNameMap _) fun acc nt => return acc.insert (← nt.qualified) nt
  let namePairCmp | (a₁, a₂), (b₁, b₂) => Name.quickCmp a₁ b₁ |>.«then» <| Name.quickCmp a₂ b₂
  let nts ← nts.mapM fun nt => do
    if nt.substitutions.isNone then
      return nt

    let mut substitutions' := RBTree.empty (cmp := namePairCmp)
    for n in ← nt.shallowClosure ntsMap do
      let substitutions? ← match ntsMap.find? n with
        | some { substitutions, .. } => pure substitutions
        | none =>
          let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n | continue
          pure substitutions
      let some substitutions := substitutions? | continue
      for subst in substitutions do
        substitutions' := substitutions'.insert subst
    return { nt with substitutions := substitutions'.toArray : NonTerminal }

  for nt@{ canon, aliases, prods, parent?, substitutions } in nts do
    -- Add symbol to environment extension.
    let normalProds := prods.foldl (init := mkNameMap _) fun acc { name, ir, type, .. } =>
      if let .normal := type then acc.insert name.getId ir else acc
    setEnv <| symbolExt.addEntry (← getEnv)
      { qualified := ← nt.qualified, normalProds, substitutions := substitutions.getD #[] }

    let isLocallyNameless (varName : Name) : CommandElabM Bool :=
      return metaVarExt.getState (← getEnv) |>.find! varName

    -- Define production and substitution parsers.
    let canonName := canon.getId
    let attrIdent := mkIdent <| ← nt.parserAttrName
    if parent?.isNone then
      for { name, ir, .. } in prods do
        let (val, type) ← IR.toParser ir nt.canon.getId symbolPrefix
        let parserIdent := mkIdentFrom name <| canonName ++ name.getId |>.appendAfter "_parser"
        elabCommand <| ← `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : $type := $val)

      for (varName, valName) in substitutions.getD #[] do
        let parserIdent := mkIdent <| canonName ++ varName |>.appendAfter "_subst_parser"
        elabCommand <| ←
          `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : TrailingParser :=
              trailingNode $(quote <| ← nt.catName) Parser.maxPrec 0 <|
                "[" >> categoryParser $(quote <| symbolPrefix ++ valName) 0 >> " / " >>
                  categoryParser $(quote <| symbolPrefix ++ varName) 0 >> "]")

        -- Also add open parsers for this variable if it's locally nameless.
        if !(← isLocallyNameless varName) then
          continue

        let parserIdent := mkIdent <| canonName ++ varName |>.appendAfter "_open_parser"
        elabCommand <| ←
          `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : TrailingParser :=
              trailingNode $(quote <| ← nt.catName) Parser.maxPrec 0 <|
                "^" >> categoryParser $(quote <| symbolPrefix ++ varName) 0)

        let parserIdent := mkIdent <| canonName ++ valName |>.appendAfter "_open_parser"
        elabCommand <| ←
          `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : TrailingParser :=
              trailingNode $(quote <| ← nt.catName) Parser.maxPrec 0 <|
                "^^" >> categoryParser $(quote <| symbolPrefix ++ valName) 0)

        let parserIdent := mkIdent <| canonName ++ varName |>.appendAfter "_close_parser"
        elabCommand <| ←
          `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : Parser :=
              leadingNode $(quote <| ← nt.catName) Parser.maxPrec <|
                "\\" >> categoryParser $(quote <| symbolPrefix ++ varName) 0 >> "^" >>
                  categoryParser $(quote <| ← nt.catName) 0)

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
            categoryParser $(quote <| ← nt.varCatName) Parser.maxPrec >>
            Parser.optional (checkLineEq >> "@" >> checkLineEq >> Parser.ident))

    -- Define parser in parent.
    if let some parent' := parent? then
      let parentQualified := parent'.getId
      let parentParserCatName := symbolPrefix ++ parentQualified
      let parentParserAttrName := parentParserCatName.appendAfter "_parser"
      let parentParserIdent :=
        mkIdentFrom parent' <| `_root_ ++ parentQualified ++ canonName.appendAfter "_parser"
      elabCommand <| ←
        `(@[$(mkIdent parentParserAttrName):ident] def $parentParserIdent : Parser :=
            leadingNode $(quote parentParserCatName) Parser.maxPrec <|
              categoryParser $(quote <| ← nt.catName) 0)

    -- Define desugar macros and elaboration.
    let catIdent := mkIdent <| ← nt.catName
    let termProdMatchAlts ← if parent?.isSome then pure #[] else
      prods.filterMapM fun prod@{ name, ir, type, ids, .. } => do
        let patternArgs ← IR.toPatternArgs ir

        if let .sugar desugar' := type then
          let macroIdent := mkIdentFrom name <| canonName ++ name.getId |>.appendAfter "_macro"
          elabCommand <| ←
            `(@[macro $catIdent] def $macroIdent : Lean.Macro
                | Lean.Syntax.node _ $(quote <| ← nt.catName) #[$patternArgs,*] => $desugar'
                | _ => Lean.Macro.throwUnsupported)
          return none

        let seqItems ← IR.toTermSeqItems ir canon.getId ids prod.binders
        let exprArgs ← IR.toExprArgs ir ids prod.binders
        let rest ← if let .customElab elab' := type then
            pure elab'
          else
            `(term| return Lean.mkAppN
                      (Lean.Expr.const $(quote <| ns ++ canonName ++ name.getId) [])
                      #[$exprArgs,*])

        `(matchAltExpr|
          | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[$patternArgs,*] => do
            $seqItems*
            $rest:term)

    let substName (varName : Name) := varName.replacePrefix ns .anonymous |>.appendAfter "_subst"
    let termSubstMatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.mapM fun (varName, valName) => do
        `(matchAltExpr|
            | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                Lean.Syntax.atom _ "[",
                val@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ valName) _),
                Lean.Syntax.atom _ "/",
                var@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ varName) _),
                Lean.Syntax.atom _ "]"
              ] => do
              let baseExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ ns ++ canonName) false base
              let varExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ varName) true var
              let valExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ valName) false val
              return Lean.mkApp3 (Expr.const $(quote <| ns ++ canonName ++ substName varName) []) baseExpr varExpr valExpr)

    let openName (varName : Name) := varName.replacePrefix ns .anonymous |>.appendAfter "_open"
    let termOpenMatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.filterMapM fun (varName, _) => do
        if !(← isLocallyNameless varName) then return none

        return some <| ←
          `(matchAltExpr|
            | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                Lean.Syntax.atom _ "^",
                var@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ varName) _)
              ] => do
              let baseExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ ns ++ canonName) false base
              let varExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ varName) true var
              return Lean.mkApp3 (Expr.const $(quote <| ns ++ canonName ++ openName varName) []) baseExpr varExpr <| Expr.lit <| Literal.natVal 0)

    let termOpen'MatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.filterMapM fun (varName, valName) => do
        if !(← isLocallyNameless varName) then return none

        return some <| ←
          `(matchAltExpr|
            | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                Lean.Syntax.atom _ "^^",
                val@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ valName) _)
              ] => do
              let baseExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ ns ++ canonName) false base
              let valExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ valName) false val
              return Lean.mkApp3 (Expr.const $(quote <| ns ++ canonName ++ openName valName) []) baseExpr valExpr <| Expr.lit <| Literal.natVal 0)

    let closeName (varName : Name) := varName.replacePrefix ns .anonymous |>.appendAfter "_close"
    let termCloseMatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.filterMapM fun (varName, _) => do
        if !(← isLocallyNameless varName) then return none

        return some <| ←
          `(matchAltExpr|
            | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                Lean.Syntax.atom _ "\\",
                var@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ varName) _),
                Lean.Syntax.atom _ "^",
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _)
              ] => do
              let varExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ varName) true var
              let baseExpr ← Lott.DSL.Elab.elabTerm $(quote <| symbolPrefix ++ ns ++ canonName) false base
              return Lean.mkApp3 (Expr.const $(quote <| ns ++ canonName ++ closeName varName) []) baseExpr varExpr <| Expr.lit <| Literal.natVal 0)

    let termElabIdent := mkIdentFrom canon <| canonName.appendAfter "TermElab"
    elabCommand <| ←
      `(@[lott_term_elab $catIdent] def $termElabIdent : Lott.DSL.Elab.TermElab
          $termProdMatchAlts:matchAlt*
          $termSubstMatchAlts:matchAlt*
          $termOpenMatchAlts:matchAlt*
          $termOpen'MatchAlts:matchAlt*
          $termCloseMatchAlts:matchAlt*
          | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
              Lean.Syntax.node _ $(quote <| ← nt.varCatName) #[ident@(Lean.Syntax.ident ..)],
              Lean.Syntax.node _ `null #[]
            ] => do
            let type ← Lean.Elab.Term.elabType <| mkIdent $(quote <| ns ++ canonName)
            Lean.Elab.Term.elabTerm ident type
          | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
              Lean.Syntax.node _ $(quote <| ← nt.varCatName) #[fun'@(Lean.Syntax.ident ..)],
              Lean.Syntax.node _ `null #[Lean.Syntax.atom _ "@", i@(Lean.Syntax.ident ..)]
            ] => do
            let type ← Lean.Elab.Term.elabType <| mkIdent $(quote <| ns ++ canonName)
            let natType := Expr.const `Nat []
            let funType := Expr.forallE `x natType type .default
            let funExpr ← Lean.Elab.Term.elabTerm fun' funType
            let idxExpr ← Lean.Elab.Term.elabTerm i natType
            return Expr.app funExpr idxExpr
          | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

    let texProdMatchAlts ← if parent?.isSome then pure #[] else prods.mapM fun { ir, .. } => do
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTexSeqItems ir canon.getId
      let joinArgs := IR.toJoinArgs ir

      `(matchAltExpr| | ref, Lean.Syntax.node _ $(quote <| ← nt.catName) #[$patternArgs,*] => do
          $seqItems*
          return String.join [$joinArgs,*])

    let texSubstMatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[]|>.mapM fun (varName, valName) => do
        `(matchAltExpr|
            | ref, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                Lean.Syntax.atom _ "[",
                val@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ valName) _),
                Lean.Syntax.atom _ "/",
                var@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ varName) _),
                Lean.Syntax.atom _ "]"
              ] => do
              let baseString ← Lott.DSL.Elab.elabTex $(quote <| symbolPrefix ++ ns ++ canonName) ref base
              let valString ← Lott.DSL.Elab.elabTex $(quote <| symbolPrefix ++ valName) ref val
              let varString ← Lott.DSL.Elab.elabTex $(quote <| symbolPrefix ++ varName) ref var
              return baseString ++ " [" ++ valString ++ " / " ++ varString ++ "]")

    let texOpenMatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.filterMapM fun (varName, _) => do
        if !(← isLocallyNameless varName) then return none

        return some <| ←
          `(matchAltExpr|
              | ref, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                  base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                  Lean.Syntax.atom _ "^",
                  var@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ varName) _)
                ] => do
                let baseString ← Lott.DSL.Elab.elabTex $(quote <| symbolPrefix ++ ns ++ canonName) ref base
                let varString ← Lott.DSL.Elab.elabTex $(quote <| symbolPrefix ++ varName) ref var
                return baseString ++ "^{" ++ varString ++ "}")

    let texOpen'MatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.filterMapM fun (varName, valName) => do
        if !(← isLocallyNameless varName) then return none

        return some <| ←
          `(matchAltExpr|
              | ref, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                  base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                  Lean.Syntax.atom _ "^^",
                  val@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ valName) _)
                ] => do
                let baseString ← Lott.DSL.Elab.elabTex $(quote <| symbolPrefix ++ ns ++ canonName) ref base
                let valString ← Lott.DSL.Elab.elabTex $(quote <| symbolPrefix ++ valName) ref val
                return baseString ++ "^{" ++ valString ++ "}")

    let texElabName := mkIdentFrom canon <| canon.getId.appendAfter "TexElab"
    elabCommand <| ←
      `(@[lott_tex_elab $catIdent] def $texElabName : Lott.DSL.Elab.TexElab
          $texProdMatchAlts:matchAlt*
          $texSubstMatchAlts:matchAlt*
          $texOpenMatchAlts:matchAlt*
          $texOpen'MatchAlts:matchAlt*
          | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
              Lean.Syntax.node _ $(quote <| ← nt.varCatName) #[Lean.Syntax.ident _ _ n _],
              Lean.Syntax.node _ `null #[]
            ] => return Lott.DSL.Elab.texEscape <| n.toString (escape := false)
          | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
              Lean.Syntax.node _ $(quote <| ← nt.varCatName) #[Lean.Syntax.ident _ _ n _],
              Lean.Syntax.node _ `null #[Lean.Syntax.atom _ "@", Lean.Syntax.ident _ _ i _]
            ] => do
            let n := Lott.DSL.Elab.texEscape (n.toString (escape := false))
            let i := Lott.DSL.Elab.texEscape (i.toString (escape := false))
            return "{" ++ n ++ "}_{" ++ i ++ "}"
          | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

    if let some parent' := parent? then
      let qualified ← nt.qualified
      let catName ← nt.catName
      let parentQualified := parent'.getId
      let parentCatName := symbolPrefix ++ parentQualified
      let parentCatIdent := mkIdent parentCatName
      let parentTermElabName :=
        mkIdent <| `_root_ ++ parentQualified ++ canon.getId.appendAfter "TermElab"
      elabCommand <| ←
        `(@[lott_term_elab $parentCatIdent] def $parentTermElabName : Lott.DSL.Elab.TermElab
            | _, Lean.Syntax.node _ $(quote parentCatName) #[
                stx@(Lean.Syntax.node _ $(quote <| ← nt.catName) _)
              ] => do
              let type ← Lean.Elab.Term.elabType <| mkIdent $(quote qualified)
              let e ← Lott.DSL.Elab.elabTerm $(quote catName) false stx
              return Lean.Expr.proj `Subtype 0 e
            | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

      let parentTexElabName :=
        mkIdent <| `_root_ ++ parentQualified ++ canon.getId.appendAfter "TexElab"
      elabCommand <| ←
        `(@[lott_tex_elab $parentCatIdent] def $parentTexElabName : Lott.DSL.Elab.TexElab
            | ref, Lean.Syntax.node _ $(quote parentCatName) #[
                stx@(Lean.Syntax.node _ $(quote <| ← nt.catName) _)
              ] => Lott.DSL.Elab.elabTex $(quote catName) ref stx
            | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

    -- Add substitutions functions.
    if parent?.isSome then
      continue

    for subst@(varTypeName, valTypeName) in substitutions.getD #[] do
      let locallyNameless ← isLocallyNameless varTypeName
      let varTypeId := mkIdent <| if locallyNameless then
          varTypeName.appendAfter "Id"
        else
          varTypeName
      let valTypeId := mkIdent valTypeName

      let varId ← mkFreshIdent varTypeId
      let valId ← mkFreshIdent valTypeId

      let matchAlts ← prods.filterMapM fun { name, ir, type, bindConfig?, .. } => do
        let .normal := type | return none
        let prodId := mkIdent <| canon.getId ++ name.getId

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

        let patternArgAndRhsArgs ← ir.filterMapM fun (mk l ir) => do
          if some l == bindConfig?.map fun { of, .. } => of then
            return none

          match ir with
          | .category n =>
            if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
              if substitutions.contains subst then
                return some (l, ← `($(mkIdent <| n ++ substName varTypeName):ident $l $varId $valId))

            return some (l, l)
          | .atom _ =>
            if let some bindConfig := bindConfig? then
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "atoms shouldn't be referenced by binders"

            return none
          | .sepBy #[mk _ (.category n)] _ =>
            if let some bindConfig := bindConfig? then
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "sepBys shouldn't be referenced by binders"

            let mapId ← mkFreshIdent l

            return some (
              l,
              ← `(let rec $mapId:ident
                    | [] => []
                    | x :: xs => $(mkIdent <| n ++ substName varTypeName):ident x $varId $valId :: $mapId xs;
                  $mapId $l))
          | .sepBy ..
          | .optional _ =>
            throwError "substitution for productions with non-trivial sepBy or optional syntax are not supported"
        let (patternArgs, rhsArgs) := patternArgAndRhsArgs.unzip

        `(matchAltExpr| | $prodId $patternArgs* => $prodId $rhsArgs*)

      elabCommand <| ←
        `(def $(mkIdentFrom canon <| canon.getId ++ substName varTypeName)
            (x : $canon) ($varId : $varTypeId) ($valId : $valTypeId) : $canon := match x with
            $matchAlts:matchAlt*)

      -- Also add var and val open if applicable.
      if !locallyNameless then
        continue

      let idxId ← mkFreshIdent varTypeId
      let matchAlts ← prods.filterMapM fun { name, ir, type, bindConfig?, .. } => do
        let .normal := type | return none
        let prodId := mkIdent <| canon.getId ++ name.getId

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

        let patternArgAndRhsArgs ← ir.filterMapM fun (mk l ir) => do
          if some l == bindConfig?.map fun { of, .. } => of then
            return none

          match ir with
          | .category n =>
            if some l != binderId? && n == varTypeName then
              return some (l, ← `(if .bound $idxId = $l then .free $varId else $l))

            if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
              if substitutions.contains subst then
                return some (l, ← `($(mkIdent <| n ++ openName varTypeName):ident $l $varId $idxId))

            return some (l, l)
          | .atom _ =>
            if let some bindConfig := bindConfig? then
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "atoms shouldn't be referenced by binders"

            return none
          | .sepBy #[mk _ (.category n)] _ =>
            if let some bindConfig := bindConfig? then
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "sepBys shouldn't be referenced by binders"

            let mapId ← mkFreshIdent l

            return some (
              l,
              ← `(let rec $mapId:ident
                    | [] => []
                    | x :: xs => $(mkIdent <| n ++ openName varTypeName):ident x $varId $idxId :: $mapId xs;
                  $mapId $l))
          | .sepBy ..
          | .optional _ =>
            throwError "opening for productions with non-trivial sepBy or optional syntax are not supported"
        let (patternArgs, rhsArgs) := patternArgAndRhsArgs.unzip

        if binderId?.isSome then
          `(matchAltExpr|
              | x@($prodId $patternArgs*) => let $idxId := $idxId + 1; $prodId $rhsArgs*)
        else
          `(matchAltExpr| | $prodId $patternArgs* => $prodId $rhsArgs*)

      elabCommand <| ←
        `(def $(mkIdentFrom canon <| canon.getId ++ openName varTypeName)
            (x : $canon) ($varId : $varTypeId) ($idxId : Nat := 0) : $canon := match x with
            $matchAlts:matchAlt*)

      let matchAlts ← prods.filterMapM fun { name, ir, type, bindConfig?, .. } => do
        let .normal := type | return none
        let prodId := mkIdent <| canon.getId ++ name.getId

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

        let patternArgAndRhsArgs ← ir.filterMapM fun (mk l ir) => do
          if some l == bindConfig?.map fun { of, .. } => of then
            return none

          match ir with
          | .category n =>
            if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
              if substitutions.contains subst then
                return some (l, ← `($(mkIdent <| n ++ openName valTypeName):ident $l $valId $idxId))

            return some (l, l)
          | .atom _ =>
            if let some bindConfig := bindConfig? then
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "atoms shouldn't be referenced by binders"

            return none
          | .sepBy #[mk _ (.category n)] _ =>
            if let some bindConfig := bindConfig? then
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "sepBys shouldn't be referenced by binders"

            let mapId ← mkFreshIdent l

            return some (
              l,
              ← `(let rec $mapId:ident
                    | [] => []
                    | x :: xs => $(mkIdent <| n ++ openName valTypeName):ident x $valId $idxId :: $mapId xs;
                  $mapId $l))
          | .sepBy ..
          | .optional _ =>
            throwError "substitution for productions with non-trivial sepBy or optional syntax are not supported"
        let (patternArgs, rhsArgs) := patternArgAndRhsArgs.unzip

        if binderId?.isSome then
          `(matchAltExpr|
              | x@($prodId $patternArgs*) => let $idxId := $idxId + 1; $prodId $rhsArgs*)
        else
          `(matchAltExpr| | $prodId $patternArgs* => $prodId $rhsArgs*)

      elabCommand <| ←
        `(def $(mkIdentFrom canon <| canon.getId ++ openName valTypeName)
            (x : $canon) ($valId : $valTypeId) ($idxId : Nat := 0) : $canon := match x with
            $matchAlts:matchAlt*)

      let matchAlts ← prods.filterMapM fun { name, ir, type, bindConfig?, .. } => do
        let .normal := type | return none
        let prodId := mkIdent <| canon.getId ++ name.getId

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

        let patternArgAndRhsArgs ← ir.filterMapM fun (mk l ir) => do
          if some l == bindConfig?.map fun { of, .. } => of then
            return none

          match ir with
          | .category n =>
            if some l != binderId? && n == varTypeName then
              return some (l, ← `(if .free $varId = $l then .bound $idxId else $l))

            if let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n then
              if substitutions.contains subst then
                return some (l, ← `($(mkIdent <| n ++ closeName varTypeName):ident $l $varId $idxId))

            return some (l, l)
          | .atom _ =>
            if let some bindConfig := bindConfig? then
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "atoms shouldn't be referenced by binders"

            return none
          | .sepBy #[mk _ (.category n)] _ =>
            if let some bindConfig := bindConfig? then
              if let some ref := bindConfig.find? l.getId then
                throwErrorAt ref "sepBys shouldn't be referenced by binders"

            let mapId ← mkFreshIdent l

            return some (
              l,
              ← `(let rec $mapId:ident
                    | [] => []
                    | x :: xs => $(mkIdent <| n ++ closeName varTypeName):ident x $varId $idxId :: $mapId xs;
                  $mapId $l))
          | .sepBy ..
          | .optional _ =>
            throwError "closing for productions with non-trivial sepBy or optional syntax are not supported"
        let (patternArgs, rhsArgs) := patternArgAndRhsArgs.unzip

        if binderId?.isSome then
          `(matchAltExpr|
              | x@($prodId $patternArgs*) => let $idxId := $idxId + 1; $prodId $rhsArgs*)
        else
          `(matchAltExpr| | $prodId $patternArgs* => $prodId $rhsArgs*)

      elabCommand <| ←
        `(def $(mkIdentFrom canon <| canon.getId ++ closeName varTypeName)
            (x : $canon) ($varId : $varTypeId) ($idxId : Nat := 0) : $canon := match x with
            $matchAlts:matchAlt*)

      -- TODO: Generate locally closed and in free variables inductives automatically.

elab_rules : command
  | `($nt:Lott.DSL.NonTerminal) => elabNonTerminals #[nt]
  | `(mutual $[$nts:Lott.DSL.NonTerminal]* end) => elabNonTerminals nts

/- Judgement syntax. -/

elab_rules : command | `(judgement_syntax $[$ps]* : $name $[(id $ids?,*)]?) => do
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
    `(@[Lott.Judgement_parser, $(mkIdent parserAttrName):ident] def $parserIdent : Parser := $val)

  -- Define elaboration.
  let patternArgs ← IR.toPatternArgs ir
  let termSeqItems ← IR.toTermSeqItems ir name.getId ids #[]
  let exprArgs ← IR.toExprArgs ir ids #[]
  let catIdent := mkIdent catName
  let termElabIdent := mkIdentFrom name <| name.getId.appendAfter "TermElab"
  elabCommand <| ←
    `(@[lott_term_elab $catIdent] def $termElabIdent : Lott.DSL.Elab.TermElab
        | _, Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] => do
          $termSeqItems*
          let name := $(quote qualified)
          let some e ← Lean.Elab.Term.resolveId? <| Lean.mkIdent name
            | Lean.throwError s!"failed to resolve judgement identifier {name} (potential use of judgement embedding before judgement declaration)"
          return Lean.mkAppN e #[$exprArgs,*]
        | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

  let texSeqItems ← IR.toTexSeqItems ir name.getId
  let joinArgs := IR.toJoinArgs ir
  let texElabName := mkIdentFrom name <| name.getId.appendAfter "TexElab"
  elabCommand <| ←
    `(@[lott_tex_elab $catIdent] def $texElabName : Lott.DSL.Elab.TexElab
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
    let .some { ir, ids, .. } := judgementExt.getState (← getEnv) |>.byName.find? catName
      | throwError "judgement_syntax for {name} not given before use in judgement"

    let type ← IR.toTypeArrSeq ir (← `(term| Prop)) ids #[]
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

end Lott.DSL.Elab
