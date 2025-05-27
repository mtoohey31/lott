import Lott.Elab.Basic
import Lott.Parser

namespace Lott

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Parser
open Lean.Parser.Command
open Lean.Parser.Term
open Lott.IR

private
def symbolEmbedIdent := mkIdent ``Lott.symbolEmbed

private partial
def IR.toIsChildCtor (prodIdent isIdent : Ident) (qualified pqualified : Name) (ir pir : Array IR)
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
        .node _ `null level,
        .node _ `null _
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
  profileTex : NameMap Term

private
def Production.binders (prod : Production) : Array Name :=
  prod.bindConfig?.toArray.map fun { of, .. } => of.getId

private
structure NonTerminal where
  canon : Ident
  aliases : Array (Ident × Bool × Option String)
  prods : Array Production
  parent? : Option Ident
  substitutions? : Option (Array (Name × Name))
  texPrePost? : Option (String × String)
  profiles : Array Name

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

private partial
def shallowSubstitutionClosure (nt : NonTerminal) (qualifiedLocalMap : NameMap NonTerminal)
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

private partial
def profileClosure (nt : NonTerminal) (qualifiedLocalMap : NameMap NonTerminal)
  : CommandElabM (Array Name) := do
  let mut res : NameSet := RBTree.fromArray nt.profiles Name.quickCmp
  let mut visited : NameSet := .empty |>.insert <| ← nt.qualified
  let mut queue := #[nt]
  repeat do
    let some nt := queue.back? | break
    queue := queue.pop

    for { ir, .. } in nt.prods do
      for name in irsClosure ir do
        if visited.contains name then
          continue

        visited := visited.insert name

        if let some nt@{ profiles, .. } := qualifiedLocalMap.find? name then
          res := res.union <| .fromArray profiles Name.quickCmp
          queue := queue.push nt
        else if let some { profiles, .. } := symbolExt.getState (← getEnv) |>.find? name then
          res := res.union <| .fromArray profiles Name.quickCmp
  return res.toArray
where
  irClosure : IR → NameSet
    | .mk _ (.category n) => .empty |>.insert n
    | .mk _ (.atom _) => .empty
    | .mk _ (.sepBy ir _)
    | .mk _ (.optional ir) => irsClosure ir
  irsClosure ir := ir.foldl (·.union <| irClosure ·) .empty

end NonTerminal

set_option maxHeartbeats 2000000 in
private
def elabNonTerminals (nts : Array Syntax) : CommandElabM Unit := do
  -- Populate alias map immediately so we can resolve stuff within the current mutual throughout the
  -- following steps.
  let ns ← getCurrNamespace
  for nt in nts do
    let `(NonTerminal| $[nosubst]? nonterminal $[(parent := $parent?)]? $[(tex pre := $_, post := $_)]? $[$names $[notex]? $[(tex := $nameTex?s)]?],* := $_*) := nt
      | throwUnsupportedSyntax
    let names@(canonName :: _) := names.toList | throwUnsupportedSyntax
    let canon := ns ++ canonName.getId
    for (name, tex?) in names.zip nameTex?s.toList do
      let tex? := tex?.map TSyntax.getString
      setEnv <| aliasExt.addEntry (← getEnv) { canon, alias := ns ++ name.getId, tex? }

    if let some parent := parent? then
      let parent ← resolveSymbol parent (allowSuffix := false)
      setEnv <| childExt.addEntry (← getEnv) { canon, parent }

  -- Transform syntax into non-terminal structure.
  let nts ← nts.mapM fun nt => do
    let `(NonTerminal| $[nosubst%$ns]? nonterminal $[(parent := $parent?)]? $[(tex pre := $pre?, post := $post?)]? $[$names $[notex%$nameNt?s]? $[(tex := $nameTex?s)]?],* := $prods*) := nt
      | throwUnsupportedSyntax
    let some canon := names[0]? | throwUnsupportedSyntax
    let aliases := names.extract 1 names.size |>.zip <|
      nameNt?s.extract 1 nameNt?s.size |>.map Option.isSome |>.zip <|
      nameTex?s.extract 1 nameTex?s.size |>.map <| Option.map TSyntax.getString

    let prodSubstAndProfiles ← prods.mapM fun prod => do
      let `(Production| | $[$ps]* : $name $[nosubst%$ns?]? $[notex%$nt?]? $[(bind $of? $[in $in??,*]?)]? $[(id $ids?,*)]? $[(expand := $expand?)]? $[(tex $[$texProfile?s]? := $tex?s)]*) := prod
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

      let (_, defaults) := texProfile?s.zip tex?s |>.partition fun (p?, _) => p?.isSome
      if defaults.size > 1 then
        throwUnsupportedSyntax
      let profileTex := RBMap.fromArray (cmp := Name.quickCmp) <| texProfile?s.zip tex?s |>.map
        fun (profile?, tex) => (profile?.map TSyntax.getId |>.getD default, tex)

      return (
        { name, ir, expand?, bindConfig?, ids, «notex» := nt?.isSome, profileTex },
        subst,
        texProfile?s.filterMap id
      )

    let (prods, substAndProfiles) := prodSubstAndProfiles.unzip
    let (substs, profiless) := substAndProfiles.unzip
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

    let profiles := RBTree.toArray <| RBTree.fromArray (cmp := Name.quickCmp) <|
      profiless.flatten.map TSyntax.getId

    return { canon, aliases, prods, parent?, substitutions?, texPrePost?, profiles : NonTerminal }

  -- Define parser categories.
  for nt in nts do
    setEnv <| ← registerParserCategory (← getEnv) (← nt.parserAttrName) (← nt.catName) .symbol
    setEnv <| ← registerParserCategory (← getEnv) (← nt.varParserAttrName) (← nt.varCatName) .symbol

  -- Define mutual inductives.
  if ← getTerm then
    let defsAndInductives ← nts.mapM fun nt@{ canon, prods, parent?, .. } => do
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
  else
    for { canon, .. } in nts do
      elabCommand <| ← `(opaque $canon : Type)

  let ntsMap ← nts.foldlM (init := mkNameMap _) fun acc nt => return acc.insert (← nt.qualified) nt
  let namePairCmp | (a₁, a₂), (b₁, b₂) => Name.quickCmp a₁ b₁ |>.«then» <| Name.quickCmp a₂ b₂
  let nts ← nts.mapM fun nt => do
    if nt.substitutions?.isNone then
      return nt

    let mut substitutions' := RBTree.empty (cmp := namePairCmp)
    for n in ← nt.shallowSubstitutionClosure ntsMap do
      let substitutions? ← match ntsMap.find? n with
        | some { substitutions?, .. } => pure substitutions?
        | none =>
          let some { substitutions, .. } := symbolExt.getState (← getEnv) |>.find? n | continue
          pure substitutions
      let some substitutions := substitutions? | continue
      for subst in substitutions do
        substitutions' := substitutions'.insert subst
    return { nt with substitutions? := substitutions'.toArray : NonTerminal }

  let nts ← nts.mapM fun nt => do
    return { nt with profiles := ← nt.profileClosure ntsMap : NonTerminal }

  for nt@{ canon, aliases, prods, parent?, substitutions?, texPrePost?, profiles } in nts do
    -- Add symbol to environment extension before proceeding so that lookups of things within the
    -- current mutual still work properly.
    let normalProds := prods.foldl (init := mkNameMap _) fun acc { name, ir, expand?, .. } =>
      if expand?.isNone then acc.insert name.getId ir else acc
    setEnv <| symbolExt.addEntry (← getEnv) {
      qualified := ← nt.qualified,
      normalProds,
      substitutions := substitutions?.getD #[],
      texPrePost?,
      profiles
    }

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
                Parser.optional (checkNoWsBefore >> "#" >> checkLineEq >> Parser.numLit) >>
                Parser.optional (checkNoWsBefore >> "/" >> checkLineEq >>
                  categoryParser $(quote <| symbolPrefix ++ varName) 0))

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
    for (alias, _) in aliases do
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
    for prod@{ name, ir, expand?, ids, profileTex, .. } in prods do
      let patternArgs ← IR.toPatternArgs ir

      if ← getTerm then
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

      if ← getTexOutputSome then
        let texSeqItems ← IR.toTexSeqItems ir canon.getId
        let profileAlternatives ← profileTex.toArray.filterMapM fun (profile, tex) => do
          if profile == default then
            return none
          return some <| ← `(doSeqItem| if profile == $(quote profile) then return $tex)
        let rest ← profileTex.find? default |>.getDM do
          let joinArgs := IR.toJoinArgs ir
          `(" ".intercalate [$joinArgs,*])

        let texElabName := mkIdentFrom name <| canonName ++ name.getId.appendAfter "TexElab"
        elabCommand <| ←
          `(@[lott_tex_elab $catIdent]
            private
            def $texElabName : TexElab := fun profile ref stx => do
              let Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] := stx
                | throwUnsupportedSyntax
              $texSeqItems*
              $profileAlternatives*
              return $rest)

    if ← getTerm then
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
  if ← getTerm then
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
  for nt@{ canon, aliases, prods, texPrePost?, profiles, .. } in nts do
    for profile in profiles.push default do
      writeTexOutput (ns ++ canon.getId ++ profile) do
        let canonTex := canon.getId.getFinal.getString!.pascalToTitle.texEscape
        let (texPre, texPost) := texPrePost?.getD ("", "")
        let aliasesTex := "\\lottaliassep\n".intercalate <| aliases.toList.filterMap
          fun (alias, «notex», tex?) =>
            if «notex» then
              none
            else
              let aliasTex := tex?.getD alias.getId.getFinal.getString!.texEscape
              s!"{texPre}\\lottalias\{{aliasTex}}{texPost}\n"
        let productionTexs ← prods.filterMapM fun { name, ir, «notex», .. } => do
          if «notex» then return none

          let canonQualified := ns ++ canon.getId
          let catName ← nt.catName
          let exampleStx := mkNode catName <| ← toExampleSyntax ir canonQualified profile
          let productionTex ← liftTermElabM <|
            texElabSymbolOrJudgement catName profile name exampleStx
          return some s!"\\lottproduction\{{productionTex}}\n"
        let productionsTex := "\\lottproductionsep\n".intercalate productionTexs.toList
        return s!"\\lottnonterminal\{{canonTex}}\{\n{aliasesTex}}\{\n{productionsTex}}\n"

elab_rules : command
  | `($nt:Lott.NonTerminal) => elabNonTerminals #[nt]
  | `(mutual $[$nts:Lott.NonTerminal]* end) => elabNonTerminals nts

end Lott
