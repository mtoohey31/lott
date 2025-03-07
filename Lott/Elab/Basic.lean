import Lott.Data.List
import Lott.Data.Option
import Lott.Environment
import Lott.Parser
import Lott.IR

-- TODO: Remove unnecessary qualifications from names.
-- TODO: Delab to embeddings when possible.
-- TODO: Make hover in non-terminal work right.
-- TODO: Test stuff without locally nameless.
-- TODO: Centralize validation of bind/id usage in nonterminals.

namespace Lott.Elab

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

/- Term embedding syntax. -/

abbrev TermElab := Bool → Syntax → TermElabM Expr

private unsafe
def mkLottTermElabAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute TermElab) := do
  mkElabAttribute TermElab .anonymous `lott_term_elab `Lott `Lott.Elab.TermElab "lott" ref

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
  mkElabAttribute TexElab .anonymous `lott_tex_elab `Lott `Lott.Elab.TexElab "lott" ref

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

def texEscape (s : String) : String :=
  String.join <| s.data.map fun c => match c with
    | '&' | '%' | '$' | '#' | '_' | '{' | '}' => "\\" ++ c.toString
    | '~' => "\\textasciitilde"
    | '^' => "\\textasciicircum"
    | '\\' => "\\textbackslash"
    | _ => c.toString

private
def variablePrefix := `Lott.Variable

private
def judgementPrefix := `Lott.Judgement

private
def _root_.Lean.Name.getFinal : Name → Name
  | .anonymous => .anonymous
  | .str _ s => .str .anonymous s
  | .num _ n => .num .anonymous n

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
def _root_.Lott.IR.ofProdArg (arg : TSyntax `Lott.prodArg) : CommandElabM IR := do
  let `(prodArg| $[$l?:ident:]?$stx:stx) := arg | throwUnsupportedSyntax
  ofStx stx l?

private
def mkMkProd (entries : Array (Term × Term)) : CommandElabM (Option (Term × Term)) := do
  let some back := entries.back? | return none
  let res ← entries.foldrM (start := entries.size - 1) (init := back)
    fun (expr, type) (mkProdAcc, typeAcc) =>
    return (
      ← ``(mkApp4 (Expr.const `Prod.mk [0, 0]) $type $typeAcc $expr $mkProdAcc),
      ← ``(mkApp2 (Expr.const `Prod [0, 0]) $type $typeAcc)
    )
  return some res

private partial
def _root_.Lott.IR.toExprArgs (ir : Array IR) (ids binders : Array Name)
  : CommandElabM (TSepArray `term ",") :=
  ir.filterMapM (β := Term) fun | ir@(mk l _) => do
      if (← IR.toType ids binders ir).isNone then
        return none

      return some l

private
def elabListComprehension (symbol : TSyntax `Lott.Symbol) (pat : Term) (collection : Term)
  (type : Expr) : TermElabM Expr := do
  let stx ← `($collection |>.map (fun $pat => [[$symbol:Lott.Symbol]]) |>.flatten)
  Term.elabTerm stx <| Expr.app (.const `List [levelOne]) type

private
def elabOptionComprehension (symbol : TSyntax `Lott.Symbol) (condition : Term) (type : Expr)
  : TermElabM Expr := do
  let stx ← `([[$symbol:Lott.Symbol]].filter fun _ => $condition)
  Term.elabTerm stx <| Expr.app (.const `Option [levelOne]) type

private partial
def _root_.Lott.IR.toTermSeqItems (ir : Array IR) (canon : Name) (ids binders : Array Name)
  : CommandElabM (TSyntaxArray `Lean.Parser.Term.doSeqItem) :=
  ir.filterMapM fun
    | mk l (.category n) => do
      if binders.contains l.getId then
        return none

      `(doSeqItem|
          let $l ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ n)
            $(quote <| ids.contains l.getId) $l)
    | mk _ (.atom _) => return none
    | mk l (.sepBy ir sep) => do
      let catName := sepByPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTermSeqItems ir canon ids binders
      let exprArgs ← IR.toExprArgs ir ids binders
      let exprTypes ← ir.filterMapM <| IR.toMkTypeExpr ids binders
      let some (mkProd, type) ← mkMkProd (exprArgs.getElems.zip exprTypes) | return none

      let termElabIdent := mkIdentFrom l <| canon ++ l.getId.appendAfter "TermElab"
      elabCommand <| ←
        `(@[lott_term_elab $(mkIdent catName)] def $termElabIdent : Lott.Elab.TermElab
            | _, Syntax.node _ $(quote catName) #[
              Lean.Syntax.atom _ "</",
              symbol,
              Lean.Syntax.atom _ "//",
              pat,
              Lean.Syntax.atom _ "in",
              collection,
              Lean.Syntax.atom _ "/>"
            ] => do
              elabListComprehension (TSyntax.mk symbol) (TSyntax.mk pat) (TSyntax.mk collection) $type
            | _, Syntax.node _ $(quote catName) #[
                lhs@(Syntax.node _ $(quote catName) _),
                Lean.Syntax.atom _ $(quote sep.trim),
                rhs@(Syntax.node _ $(quote catName) _)
              ] => do
              let lhs ← Lott.Elab.elabTerm $(quote catName) false lhs
              let rhs ← Lott.Elab.elabTerm $(quote catName) false rhs
              Meta.liftMetaM <| Meta.reduceAll <| mkApp3 (Expr.const `List.append [0]) $type lhs rhs
            | _, Syntax.node _ $(quote catName) #[$patternArgs,*] => do
              $seqItems*
              return mkApp3 (Expr.const `List.cons [0]) $type $mkProd <| Expr.app (Expr.const `List.nil [0]) $type
            | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx => Lott.Elab.elabTerm $(quote catName) false stx
          | none => pure <| Expr.app (Expr.const `List.nil [0]) $type)
    | mk l (.optional ir) => do
      let catName := sepByPrefix ++ (← getCurrNamespace) ++ canon ++ l.getId |>.obfuscateMacroScopes
      let patternArgs ← IR.toPatternArgs ir
      let seqItems ← IR.toTermSeqItems ir canon ids binders
      let exprArgs ← IR.toExprArgs ir ids binders
      let exprTypes ← ir.filterMapM <| IR.toMkTypeExpr ids binders
      let some (mkProd, type) ← mkMkProd (exprArgs.getElems.zip exprTypes) | return none

      let termElabIdent := mkIdentFrom l <| canon ++ l.getId.appendAfter "TermElab"
      elabCommand <| ←
        `(@[lott_term_elab $(mkIdent catName)] def $termElabIdent : Lott.Elab.TermElab
            | _, Syntax.node _ $(quote catName) #[
              Lean.Syntax.atom _ "</",
              symbol,
              Lean.Syntax.atom _ "//",
              condition,
              Lean.Syntax.atom _ "/>"
            ] => do
              elabOptionComprehension (TSyntax.mk symbol) (TSyntax.mk condition) $type
            | _, Syntax.node _ $(quote catName) #[$patternArgs,*] => do
              $seqItems*
              return mkApp2 (Expr.const `Option.some [0]) $type $mkProd
            | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

      `(doSeqItem| let $l ← match (Syntax.getArgs $l)[0]? with
          | some stx => Lott.Elab.elabTerm $(quote catName) false stx
          | none => pure <| Expr.app (Expr.const `Option.none [0]) $type)

partial
def _root_.Lott.IR.toTexSeqItems (ir : Array IR) (canon : Name) : CommandElabM (TSyntaxArray `Lean.Parser.Term.doSeqItem) :=
  ir.mapM fun
    | mk l (.category n) => `(doSeqItem| let $l ← Lott.Elab.elabTex $(quote <| symbolPrefix ++ n) ref $l)
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

      `(doSeqItem| let $l ← Option.getD (dflt := "") <$> (Syntax.getArgs $l)[0]?.mapM fun stx => do
          let Syntax.node _ _ #[$patternArgs,*] := stx | throwUnsupportedSyntax
          $seqItems*
          return String.join [$joinArgs,*])

partial
def _root_.Lott.IR.toIsChildCtor (prodIdent isIdent : Ident) (qualified pqualified : Name) (ir pir : Array IR)
  (binders : Array Name) : CommandElabM (TSyntax `Lean.Parser.Command.ctor) := do
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
  go (irs : Array (IR × IR)) (patAcc : TSyntaxArray `Lean.binderIdent := #[])
    (propAcc : Array Term := #[])
    : CommandElabM (TSyntaxArray `Lean.binderIdent × Array Term) := do
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

      if some np == ((childExt.getState (← getEnv)).find? n).map (·.parent') then
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
      | (patArgs, props) => go irs' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $l'bi ∈ $l, let $(← foldrProd <| ← toTerms patArgs):term := $l'; $(← foldlAnd props))
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
      | (patArgs, props) => go irs' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $l'bi ∈ $l, let $(← foldrProd <| ← toTerms patArgs):term := $l'; $(← foldlAnd props))
    | _, _ => throwErrorAt prodIdent "mismatched syntax"

private
def Nat.toSubscriptString : Nat → String
  | 0 => "₀"
  | 1 => "₁"
  | 2 => "₂"
  | 3 => "₃"
  | 4 => "₄"
  | 5 => "₅"
  | 6 => "₆"
  | 7 => "₇"
  | 8 => "₈"
  | 9 => "₉"
  | n => (n / 10).toSubscriptString ++ (n % 10).toSubscriptString

private
def freeName (varName : Name) (typeName : Name) : CommandElabM Name := do
  let ns ← getCurrNamespace
  let typeName := typeName.replacePrefix ns .anonymous
  match varName.replacePrefix ns .anonymous with
  | .str .anonymous s => return typeName ++ Name.appendAfter `free s |>.appendAfter "s"
  | n => return typeName ++ `free ++ n.appendAfter "s"

partial
def toFreeMatchAlt (prodId : Ident) (ir : Array IR) (subst : Name × Name)
  (binders : Array Name) : CommandElabM (TSyntax `Lean.Parser.Term.matchAltExpr) := do
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
        return (
          l,
          ← `((List.mapMem $l fun $(← foldrProd patArgs) _ => $(← foldlAppend appendArgs)).flatten)
        )
    | .optional ir => match ← goMany ir with
      | (#[], _) => return (none, none)
      | (_, #[]) => return (← ``(_), none)
      | (patArgs, appendArgs) =>
        return (
          l,
          ← `(
            (Option.mapMem $l fun $(← foldrProd patArgs) _ => $(← foldlAppend appendArgs)).getD []
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

partial
def toLocallyClosedCtors (prodId locallyClosedId idxId : Ident) (qualified : Name) (ir : Array IR)
  (subst : Name × Name) (ids binders : Array Name)
  : CommandElabM (Array (TSyntax `Lean.Parser.Command.ctor)) := do
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
  go (irs : Array IR) (patAcc : TSyntaxArray `Lean.binderIdent := #[]) (propAcc : Array Term := #[])
    : CommandElabM (TSyntaxArray `Lean.binderIdent × Array Term) := do
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
          do `(∀ x ∈ $l, let $(← foldrProd <| ← toTerms patArgs):term := x; $prop)
        go irs (patAcc.push lbi) <| propAcc ++ propAcc'


def substName (varName : Name) : CommandElabM Name :=
  return varName.replacePrefix (← getCurrNamespace) .anonymous |>.appendAfter "_subst"

partial
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
      return some (l, ← `(List.mapMem $l fun $(← foldrProd pattern) _ => $(← foldrProd args)), true)
    | .optional ir =>
      let some (pattern, args) ←
        toSubstPatternAndArgs ir varType valType varId valId bindOf? binderId? |
        return some (l, (l : Term), false)
      let arg ← `(Option.mapMem $l fun $(← foldrProd pattern) _ => $(← foldrProd args))
      return some (l, arg, true)
  let (pats, argsAndFounds) := patsAndArgsAndFounds.unzip
  let (args, founds) := argsAndFounds.unzip
  if founds.any id then
    return some (pats, args)
  else
    return none

def openName (varName : Name) : CommandElabM Name :=
  return varName.replacePrefix (← getCurrNamespace) .anonymous |>.appendAfter "_open"

partial
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
      return some (l, ← `(List.mapMem $l fun $(← foldrProd pattern) _ => $(← foldrProd args)), true)
    | .optional ir =>
      let some (pattern, args) ←
        toVarOpenPatternAndArgs ir varType valType varId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let arg ← `(Option.mapMem $l fun $(← foldrProd pattern) _ => $(← foldrProd args))
      return some (l, arg, true)
  let (pats, argsAndFounds) := patsAndArgsAndFounds.unzip
  let (args, founds) := argsAndFounds.unzip
  if founds.any id then
    return some (pats, args)
  else
    return none

partial
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
      return some (l, ← `(List.mapMem $l fun $(← foldrProd pattern) _ => $(← foldrProd args)), true)
    | .optional ir =>
      let some (pattern, args) ←
        toValOpenPatternAndArgs ir varType valType valId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let arg ← `(Option.mapMem $l fun $(← foldrProd pattern) _ => $(← foldrProd args))
      return some (l, arg, true)
  let (pats, argsAndFounds) := patsAndArgsAndFounds.unzip
  let (args, founds) := argsAndFounds.unzip
  if founds.any id then
    return some (pats, args)
  else
    return none

def closeName (varName : Name) : CommandElabM Name :=
  return varName.replacePrefix (← getCurrNamespace) .anonymous |>.appendAfter "_close"

partial
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
      return some (l, ← `(List.mapMem $l fun $(← foldrProd pattern) _ => $(← foldrProd args)), true)
    | .optional ir =>
      let some (pattern, args) ←
        toClosePatternAndArgs ir varType valType varId idxId bindOf? binderId? |
        return some (l, (l : Term), false)
      let arg ← `(Option.mapMem $l fun $(← foldrProd pattern) _ => $(← foldrProd args))
      return some (l, arg, true)
  let (pats, argsAndFounds) := patsAndArgsAndFounds.unzip
  let (args, founds) := argsAndFounds.unzip
  if founds.any id then
    return some (pats, args)
  else
    return none

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
      `(@[$(mkIdent parserAttrName):ident] def $parserIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <| Lott.identPrefix $(quote nameStr))
    let parserIdent := mkIdentFrom alias <| canon.getId ++ aliasName.appendAfter "_idx_parser"
    elabCommand <| ←
      `(@[$(mkIdent parserAttrName):ident] def $parserIdent : TrailingParser :=
          trailingNode $(quote catName) Parser.maxPrec 0 <|
            checkNoWsBefore >> "@" >> checkLineEq >> (Parser.ident <|> Parser.numLit))
    if locallyNameless then
      let parserIdent := mkIdentFrom alias <| canon.getId ++ aliasName.appendAfter "_bound_parser"
      elabCommand <| ←
        `(@[$(mkIdent parserAttrName):ident] def $parserIdent : Parser :=
            leadingNode $(quote catName) Parser.maxPrec <|
              Lott.identPrefix $(quote nameStr) >> "$" >> num)

  -- Define elaboration.
  let catIdent := mkIdent catName
  let termElabName := mkIdentFrom canon <| canon.getId.appendAfter "TermElab"
  let (rhs, bound) ← if locallyNameless then
      pure (
        ← `(do
          if isBinder then
              let type ← Lean.Elab.Term.elabType <| mkIdent $(quote <| canonQualified.appendAfter "Id")
              Lean.Elab.Term.elabTerm ident type
            else
              let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
              let expr ← Lean.Elab.Term.elabTerm (Syntax.mkCApp `Coe.coe #[.mk ident]) type
              Meta.liftMetaM <| Meta.reduce expr),
        #[← `(matchAltExpr|
              | isBinder, Lean.Syntax.node _ $(quote catName) #[
                  ident@(Lean.Syntax.ident ..),
                  Lean.Syntax.atom _ "$",
                  num@(Lean.Syntax.node _ `num _)
                ] => do
                if isBinder then
                  throwUnsupportedSyntax
                else
                  let num ← Lean.Elab.Term.elabNumLit num <| some (.const `Nat [])
                  return (Lean.Expr.const $(quote <| canonQualified ++ `bound) []).app num)]
      )
    else
      pure (← `(do
          let type ← Lean.Elab.Term.elabType <| mkIdent $(quote canonQualified)
          Lean.Elab.Term.elabTerm ident type), #[])
  elabCommand <| ←
    `(@[lott_term_elab $catIdent] def $termElabName : Lott.Elab.TermElab
        | isBinder, Lean.Syntax.node _ $(quote catName) #[ident@(Lean.Syntax.ident ..)] => $rhs
        | isBinder, Lean.Syntax.node _ $(quote catName) #[
            Lean.Syntax.node _ $(quote catName) #[fun'@(Lean.Syntax.ident ..)],
            Lean.Syntax.atom _ "@",
            idx
          ] => do
          let typeName := if isBinder then
              $(quote <| canonQualified.appendAfter "Id")
            else
              $(quote canonQualified)
          let type ← Lean.Elab.Term.elabType <| mkIdent typeName
          let natType := Expr.const `Nat []
          let funType := Expr.forallE `x natType type .default
          let funExpr ← Lean.Elab.Term.elabTerm fun' funType
          let idxExpr ← Lean.Elab.Term.elabTerm idx natType
          return Expr.app funExpr idxExpr
        $bound:matchAlt*
        | _, stx => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)
  let texElabName := mkIdentFrom canon <| canon.getId.appendAfter "TexElab"
  elabCommand <| ←
    `(@[lott_tex_elab $catIdent] def $texElabName : Lott.Elab.TexElab
        | _, Lean.Syntax.node _ $(quote catName) #[Lean.Syntax.ident _ _ n _] => do
          return Lott.Elab.texEscape <| n.toString (escape := false)
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
    let `(NonTerminal| $[nosubst]? nonterminal $[(parent := $parent?)]? $[$names],* := $_*) := nt
      | throwUnsupportedSyntax
    let names@(canonName :: _) := names.toList | throwUnsupportedSyntax
    let canon := ns ++ canonName.getId
    for name in names do
      setEnv <| aliasExt.addEntry (← getEnv) { canon, alias := ns ++ name.getId }

    if let some parent' := parent? then
      let parent' ← resolveSymbol parent' (allowSuffix := false)
      setEnv <| childExt.addEntry (← getEnv) { canon, parent' }

  -- Transform syntax into non-terminal structure.
  let nts ← nts.mapM fun nt => do
    let `(NonTerminal| $[nosubst%$ns]? nonterminal $[(parent := $parent?)]? $[$names],* := $prods*) := nt
      | throwUnsupportedSyntax
    let some canon := names[0]? | throwUnsupportedSyntax
    let aliases := names.extract 1 names.size

    let prodAndSubsts ← prods.mapM fun prod => do
      let `(Production| | $[$ps]* : $name $[nosubst%$ns?]? $[$bindConfig?]? $[(id $ids?,*)]? $[(desugar := $desugar?)]? $[(elab := $elab?)]?) := prod
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
    let substitutions := if parent?.isSome || ns.isSome then
        none
      else
        substs.filterMap id |>.map ((·, qualified))

    let parent? ← parent?.mapM fun parent' =>
      return mkIdentFrom parent' <| ← resolveSymbol parent' (allowSuffix := false)

    return { canon, aliases, prods, parent?, substitutions : NonTerminal }

  -- Define mutual inductives and parser categories.
  let defsAndInductives ← nts.mapM fun nt@{ canon, prods, parent?, .. } => do
    setEnv <| ← registerParserCategory (← getEnv) (← nt.parserAttrName) (← nt.catName) .symbol
    setEnv <| ← registerParserCategory (← getEnv) (← nt.varParserAttrName) (← nt.varCatName) .symbol

    let some parent' := parent? |
      let ctors ← prods.filterMapM fun prod@{ name, ir, type, ids, .. } => do
        let .normal := type | return none
        let ctorType ← IR.toTypeArrSeq ir canon ids prod.binders
        `(ctor| | $name:ident : $ctorType)
      let inductive' ← `(inductive $canon where $ctors*)
      return (none, inductive')
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
    let inductive' ←
      `(inductive $(mkIdentFrom isIdent <| `_root_ ++ isIdent.getId) : $parent' → Prop where
          $ctors*)

    return (some <| ← `(def $canon := { x : $parent' // $isIdent x }), inductive')
  let (defs, inductives) := defsAndInductives.unzip
  elabMutualCommands inductives
  elabMutualCommands <| defs.filterMap id

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
    -- Add symbol to environment extension before proceeding so that lookups of things within the
    -- current mutual still work properly.
    let normalProds := prods.foldl (init := mkNameMap _) fun acc { name, ir, type, .. } =>
      if let .normal := type then acc.insert name.getId ir else acc
    setEnv <| symbolExt.addEntry (← getEnv)
      { qualified := ← nt.qualified, normalProds, substitutions := substitutions.getD #[] }

  let isLocallyNameless (varName : Name) : CommandElabM Bool :=
    return metaVarExt.getState (← getEnv) |>.find! varName

  for nt@{ canon, aliases, prods, parent?, substitutions } in nts do
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
              checkNoWsBefore >> "^" >> categoryParser $(quote <| symbolPrefix ++ varName) 0 >>
              Parser.optional (checkNoWsBefore >> "#" >> checkLineEq >> Parser.numLit))

      let parserIdent := mkIdent <| canonName ++ valName |>.appendAfter "_open_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : TrailingParser :=
            trailingNode $(quote <| ← nt.catName) Parser.maxPrec 0 <|
              checkNoWsBefore >> "^^" >> categoryParser $(quote <| symbolPrefix ++ valName) 0 >>
              Parser.optional (checkNoWsBefore >> "#" >> checkLineEq >> Parser.numLit))

      let parserIdent := mkIdent <| canonName ++ varName |>.appendAfter "_close_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $attrIdent:ident] def $parserIdent : Parser :=
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
        `(@[$varAttrIdent:ident] def $parserIdent : Parser :=
            leadingNode $(quote <| ← nt.varCatName) Parser.maxPrec <|
              Lott.identPrefix $(quote nameStr))

    -- TODO: Should this have `Lott.Symbol_parser`?
    let varParserIdent := mkIdentFrom canon <| canonName.appendAfter "_variable_parser"
    elabCommand <| ←
      `(@[$attrIdent:ident] def $varParserIdent : Parser :=
          leadingNode $(quote <| ← nt.catName) Parser.maxPrec <|
            categoryParser $(quote <| ← nt.varCatName) Parser.maxPrec >>
            Parser.optional
              (checkNoWsBefore >> "@" >> checkLineEq >> (Parser.ident <|> Parser.numLit)))

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

    let termSubstMatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.mapM fun (varName, valName) => do
        let substName := ns ++ canonName ++ (← substName varName)
        `(matchAltExpr|
            | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                Lean.Syntax.atom _ "[",
                val@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ valName) _),
                Lean.Syntax.atom _ "/",
                var@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ varName) _),
                Lean.Syntax.atom _ "]"
              ] => do
              let baseExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ ns ++ canonName) false base
              let varExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ varName) true var
              let valExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ valName) false val
              return Lean.mkApp3 (Expr.const $(quote substName) []) baseExpr varExpr valExpr)

    let termOpenMatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.filterMapM fun (varName, _) => do
        if !(← isLocallyNameless varName) then return none

        let openName := ns ++ canonName ++ (← openName varName)
        return some <| ←
          `(matchAltExpr|
            | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                Lean.Syntax.atom _ "^",
                var@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ varName) _),
                Lean.Syntax.node _ `null level
              ] => do
              let baseExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ ns ++ canonName) false base
              let varExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ varName) true var
              let natType := Expr.const `Nat []
              let lvlExpr? ← level[1]?.mapM fun lvl => Lean.Elab.Term.elabTerm lvl natType
              return Lean.mkApp3 (Expr.const $(quote openName) []) baseExpr varExpr <|
                lvlExpr?.getD <| Expr.lit <| Literal.natVal 0)

    let termOpen'MatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.filterMapM fun (varName, valName) => do
        if !(← isLocallyNameless varName) then return none

        let openName := ns ++ canonName ++ (← openName valName)
        return some <| ←
          `(matchAltExpr|
            | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _),
                Lean.Syntax.atom _ "^^",
                val@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ valName) _),
                Lean.Syntax.node _ `null level
              ] => do
              let baseExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ ns ++ canonName) false base
              let valExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ valName) false val
              let natType := Expr.const `Nat []
              let lvlExpr? ← level[1]?.mapM fun lvl => Lean.Elab.Term.elabTerm lvl natType
              return Lean.mkApp3 (Expr.const $(quote openName) []) baseExpr valExpr <|
                lvlExpr?.getD <| Expr.lit <| Literal.natVal 0)

    let termCloseMatchAlts ← if parent?.isSome then pure #[] else
      substitutions.getD #[] |>.filterMapM fun (varName, _) => do
        if !(← isLocallyNameless varName) then return none

        let closeName := ns ++ canonName ++ (← closeName varName)
        return some <| ←
          `(matchAltExpr|
            | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
                Lean.Syntax.atom _ "\\",
                var@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ varName) _),
                Lean.Syntax.node _ `null level,
                Lean.Syntax.atom _ "^",
                base@(Lean.Syntax.node _ $(quote <| ← nt.catName) _)
              ] => do
              let varExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ varName) true var
              let baseExpr ← Lott.Elab.elabTerm $(quote <| symbolPrefix ++ ns ++ canonName) false base
              let natType := Expr.const `Nat []
              let lvlExpr? ← level[1]?.mapM fun lvl => Lean.Elab.Term.elabTerm lvl natType
              return Lean.mkApp3 (Expr.const $(quote closeName) []) baseExpr varExpr <|
                lvlExpr?.getD <| Expr.lit <| Literal.natVal 0)

    let termElabIdent := mkIdentFrom canon <| canonName.appendAfter "TermElab"
    elabCommand <| ←
      `(@[lott_term_elab $catIdent] def $termElabIdent : Lott.Elab.TermElab
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
              Lean.Syntax.node _ `null #[Lean.Syntax.atom _ "@", idx]
            ] => do
            let type ← Lean.Elab.Term.elabType <| mkIdent $(quote <| ns ++ canonName)
            let natType := Expr.const `Nat []
            let funType := Expr.forallE `x natType type .default
            let funExpr ← Lean.Elab.Term.elabTerm fun' funType
            let idxExpr ← Lean.Elab.Term.elabTerm idx natType
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
              let baseString ← Lott.Elab.elabTex $(quote <| symbolPrefix ++ ns ++ canonName) ref base
              let valString ← Lott.Elab.elabTex $(quote <| symbolPrefix ++ valName) ref val
              let varString ← Lott.Elab.elabTex $(quote <| symbolPrefix ++ varName) ref var
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
                let baseString ← Lott.Elab.elabTex $(quote <| symbolPrefix ++ ns ++ canonName) ref base
                let varString ← Lott.Elab.elabTex $(quote <| symbolPrefix ++ varName) ref var
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
                let baseString ← Lott.Elab.elabTex $(quote <| symbolPrefix ++ ns ++ canonName) ref base
                let valString ← Lott.Elab.elabTex $(quote <| symbolPrefix ++ valName) ref val
                return baseString ++ "^{" ++ valString ++ "}")

    let texElabName := mkIdentFrom canon <| canon.getId.appendAfter "TexElab"
    elabCommand <| ←
      `(@[lott_tex_elab $catIdent] def $texElabName : Lott.Elab.TexElab
          $texProdMatchAlts:matchAlt*
          $texSubstMatchAlts:matchAlt*
          $texOpenMatchAlts:matchAlt*
          $texOpen'MatchAlts:matchAlt*
          | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
              Lean.Syntax.node _ $(quote <| ← nt.varCatName) #[Lean.Syntax.ident _ _ n _],
              Lean.Syntax.node _ `null #[]
            ] => return Lott.Elab.texEscape <| n.toString (escape := false)
          | _, Lean.Syntax.node _ $(quote <| ← nt.catName) #[
              Lean.Syntax.node _ $(quote <| ← nt.varCatName) #[Lean.Syntax.ident _ _ n _],
              Lean.Syntax.node _ `null #[Lean.Syntax.atom _ "@", Lean.Syntax.ident _ _ i _]
            ] => do
            let n := Lott.Elab.texEscape (n.toString (escape := false))
            let i := Lott.Elab.texEscape (i.toString (escape := false))
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
        `(@[lott_term_elab $parentCatIdent] def $parentTermElabName : Lott.Elab.TermElab
            | _, Lean.Syntax.node _ $(quote parentCatName) #[
                stx@(Lean.Syntax.node _ $(quote <| ← nt.catName) _)
              ] => do
              let type ← Lean.Elab.Term.elabType <| mkIdent $(quote qualified)
              let e ← Lott.Elab.elabTerm $(quote catName) false stx
              return Lean.Expr.proj `Subtype 0 e
            | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

      let parentTexElabName :=
        mkIdent <| `_root_ ++ parentQualified ++ canon.getId.appendAfter "TexElab"
      elabCommand <| ←
        `(@[lott_tex_elab $parentCatIdent] def $parentTexElabName : Lott.Elab.TexElab
            | ref, Lean.Syntax.node _ $(quote parentCatName) #[
                stx@(Lean.Syntax.node _ $(quote <| ← nt.catName) _)
              ] => Lott.Elab.elabTex $(quote catName) ref stx
            | _, _ => no_error_if_unused% Lean.Elab.throwUnsupportedSyntax)

  -- Add metavar functions.
  let allSubstitutions := nts.map fun { substitutions, .. } => substitutions.getD #[]
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

    let substDefs ← nts.filterMapM fun nt@{ canon, aliases, prods, parent?, substitutions } => do
      if !(substitutions.getD #[]).contains subst then
        return none

      let matchAlts ← prods.filterMapM fun { name, ir, type, bindConfig?, .. } => do
        let .normal := type | return none
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

    let varOpenDefs ← nts.filterMapM fun nt@{ canon, aliases, prods, parent?, substitutions } => do
      if !(substitutions.getD #[]).contains subst then
        return none

      let matchAlts ← prods.filterMapM fun { name, ir, type, bindConfig?, .. } => do
        let .normal := type | return none
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

    let valOpenDefs ← nts.filterMapM fun nt@{ canon, aliases, prods, parent?, substitutions } => do
      if !(substitutions.getD #[]).contains subst then
        return none

      let matchAlts ← prods.filterMapM fun { name, ir, type, bindConfig?, .. } => do
        let .normal := type | return none
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

    let closeDefs ← nts.filterMapM fun nt@{ canon, aliases, prods, parent?, substitutions } => do
      if !(substitutions.getD #[]).contains subst then
        return none

      let matchAlts ← prods.filterMapM fun { name, ir, type, bindConfig?, .. } => do
        let .normal := type | return none
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
      nts.filterMapM fun nt@{ canon, aliases, prods, parent?, substitutions } => do
        if !(substitutions.getD #[]).contains subst then
          return none

        let freeId := mkIdent <| ← freeName varTypeName <| ← nt.qualified
        let matchAlts ← prods.filterMapM fun prod@{ name, ir, type, .. } => do
          let .normal := type | return none
          let prodId := mkIdentFrom name <| (← nt.qualified) ++ name.getId
          toFreeMatchAlt prodId ir subst prod.binders
        return some <| ← `(def $freeId : $canon → List $varTypeId $matchAlts:matchAlt*)

    elabMutualCommands freeDefs

    let locallyClosedInductives ←
      nts.filterMapM fun nt@{ canon, aliases, prods, parent?, substitutions } => do
        if !(substitutions.getD #[]).contains subst then
          return none

        let locallyClosedId := mkIdent <| ← locallyClosedName varTypeName <| ← nt.qualified
        let ctors ← prods.mapM fun prod@{ name, ir, type, ids, .. } => do
          let .normal := type | return #[]
          toLocallyClosedCtors name locallyClosedId idxId (← nt.qualified) ir subst ids prod.binders
        return some <| ←
          `(inductive $locallyClosedId : $canon → (optParam Nat 0) → Prop where $ctors.flatten*)

    elabMutualCommands locallyClosedInductives

elab_rules : command
  | `($nt:Lott.NonTerminal) => elabNonTerminals #[nt]
  | `(mutual $[$nts:Lott.NonTerminal]* end) => elabNonTerminals nts

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
    `(@[lott_term_elab $catIdent] def $termElabIdent : Lott.Elab.TermElab
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
    `(@[lott_tex_elab $catIdent] def $texElabName : Lott.Elab.TexElab
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
      let `(InferenceRule| $jms:Lott.Judgement* $[─]* $name $binders* $conclusion:Lott.Judgement) := rule
        | throwUnsupportedSyntax
      let conclusionKind := conclusion.raw.getKind
      let expectedKind := judgementPrefix ++ catName
      if conclusionKind != expectedKind then
        throwErrorAt conclusion "found conclusion judgement syntax kind{indentD conclusionKind}\nexpected to find kind{indentD expectedKind}\nall conclusions of inference rules in a judgement declaration must be the judgement which is being defined"
      let ctorType ← jms.foldrM (init := ← `(term| [[$conclusion:Lott.Judgement]]))
        fun «judgement» acc => `([[$«judgement»:Lott.Judgement]] → $acc)
      `(ctor| | $name:ident $binders* : $ctorType)
    `(inductive $name : $type where $ctors*)
  elabMutualCommands inductives

elab_rules : command
  | `($jd:Lott.JudgementDecl) => elabJudgementDecls #[jd]
  | `(mutual $[$jds:Lott.JudgementDecl]* end) => elabJudgementDecls jds

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

end Lott.Elab
