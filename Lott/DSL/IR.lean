import Lean

namespace Lott.DSL

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Syntax
open Lean.Parser
open Lean.Parser.Term

def symbolPrefix := `Lott.Symbol

def sepByPrefix := `Lott.SepBy

-- Useful for avoiding "un-uniqueification" resulting from the use of `eraseMacroScopes`.
def _root_.Lean.Name.obfuscateMacroScopes (n : Name) : Name :=
    let scopesView := extractMacroScopes n
    scopesView.scopes.foldl (.str · <| toString ·) scopesView.name

-- TODO: Is there a way to use Lean's existing parser resolution instead of this custom stuff?

mutual
private
inductive IRType where
  | category (n : Name)
  | atom (s : String)
  | sepBy (ir : Array IR) (sep : String)
  | optional (ir : Array IR)
deriving Inhabited, BEq

inductive IR where
  | mk (l : Ident) (t : IRType)
deriving Inhabited, BEq
end

namespace IR

mutual
private partial
def toParser' (canon : Name) : IR → CommandElabM Term
  | mk _ (.category n) => ``(categoryParser $(quote <| symbolPrefix ++ n) Parser.maxPrec)
  | mk _ (.atom s) => ``(symbol $(mkStrLit s))
  | mk l (.sepBy ir sep) => do
    let canon' := canon ++ l.getId |>.obfuscateMacroScopes
    let catName := sepByPrefix ++ (← getCurrNamespace) ++ canon'
    let parserAttrName := catName.appendAfter "_parser"

    setEnv <| ← Parser.registerParserCategory (← getEnv) parserAttrName catName .symbol

    let attrIdent := mkIdent parserAttrName
    let (val, type) ← toParser ir canon' sepByPrefix
    if type != (← `(term| Parser)) then throwError "invalid left recursive sepBy syntax"
    let parserIdent := mkIdentFrom l <| canon'.appendAfter "_parser"
    elabCommand <| ← `(@[$attrIdent:ident] def $parserIdent : Parser := $val)

    let comprehensionIdent := mkIdentFrom l <| canon'.appendAfter "_comprehension_parser"
    elabCommand <| ←
      `(@[$attrIdent:ident] def $comprehensionIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <|
            "</ " >> withPosition (categoryParser $(quote catName) 0) >>
            " // " >> Parser.ident >> " ∈ " >> termParser >> " />")

    let sepIdent := mkIdentFrom l <| canon'.appendAfter "_sep_parser"
    elabCommand <| ←
      `(@[$attrIdent:ident] def $sepIdent : TrailingParser :=
          trailingNode $(quote catName) Parser.maxPrec 0 <|
            checkLineEq >> $(quote sep) >> categoryParser $(quote catName) 0)

    ``(Parser.optional (categoryParser $(quote catName) 0))
  | mk _ (.optional ir) => do ``(Parser.optional $(← toParserSeq canon ir))

private partial
def toParserSeq (canon : Name) (ir : Array IR) : CommandElabM Term := do
  if ir.size == 0 then
    throwUnsupportedSyntax

  ir.foldlM (start := 1) (init := ← ir[0]!.toParser' canon)
    fun acc ir => do ``($acc >> checkLineEq >> $(← ir.toParser' canon))

partial
def toParser (ir : Array IR) (canon catPrefix : Name) : CommandElabM (Term × Term) := do
  let qualified := (← getCurrNamespace) ++ canon
  let catName := catPrefix ++ qualified
  if let some (mk _ (.category n)) := ir[0]? then
    if n == qualified then
      let rest ← toParserSeq canon <| ir.extract 1 ir.size
      return (
        ← ``(trailingNode $(quote catName) Parser.maxPrec 0 <| checkLineEq >> $rest),
        ← ``(TrailingParser),
      )

  if let some (mk _ (.optional _)) := ir[0]? then
    throwError "unsupported optionally left recursive syntax"

  let rest ← toParserSeq canon ir
  return (← ``(leadingNode $(quote catName) Parser.maxPrec $rest), ← ``(Parser))
end

mutual
partial
def toType : IR → CommandElabM (Option Term)
  | IR.mk _ (.category n) => return some <| mkIdent n
  | IR.mk _ (.atom _) => return none
  | IR.mk _ (.sepBy ir _) => do
    let some type' ← toTypeProdSeq ir | return none
    ``(List $type')
  | IR.mk _ (.optional ir) => do
    let some type' ← toTypeProdSeq ir | return none
    return some <| ← ``(Option $type')

partial
def toTypeProdSeq (ir : Array IR) : CommandElabM (Option Term) := do
  let types ← ir.filterMapM IR.toType
  let some (type' : Term) := types[0]? | return none
  return some <| ← types.foldlM (start := 1) (init := type') fun acc t => ``($acc × $t)
end

mutual
partial
def toMkTypeExpr : IR → CommandElabM (Option Term)
  | IR.mk _ (.category n) => ``(Expr.const $(quote n) [])
  | IR.mk _ (.atom _) => return none
  | IR.mk _ (.sepBy ir _) => do
    let some type' ← toMkTypeProdSeqExpr ir | return none
    ``(mkApp (Expr.const `List [levelOne]) $type')
  | IR.mk _ (.optional ir) => do
    let some type' ← toMkTypeProdSeqExpr ir | return none
    ``(mkApp (Expr.const `Option [levelOne]) $type')

partial
def toMkTypeProdSeqExpr (ir : Array IR) : CommandElabM (Option Term) := do
  let types ← ir.filterMapM IR.toMkTypeExpr
  let some back := types.back? | return none
  types.foldrM (start := types.size - 1) (β := Term) (init := back) fun t acc =>
    ``(mkApp2 (Expr.const `Prod [levelOne, levelOne]) $t $acc)
end

def toTypeArrSeq (ir : Array IR) (init : Term) : CommandElabM Term := do
  (← ir.filterMapM IR.toType) |>.foldrM (init := init) fun t acc => ``($t → $acc)

private
def toPatternArg : IR → CommandElabM Term
  | mk l (.category n) => `($l@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ n) _))
  | mk l (.atom s) => `($l@(Lean.Syntax.atom _ $(quote s.trim)))
  | mk l (.sepBy ..) => `($l@(Lean.Syntax.node _ `null _))
  | mk l (.optional ..) => `($l@(Lean.Syntax.node _ `null _))

def toPatternArgs (ir : Array IR) : CommandElabM (TSepArray `term ",") :=
  ir.mapM IR.toPatternArg

def toJoinArgs (ir : Array IR) : TSepArray `term "," := ir.map (β := Term) fun | mk l _ => l

partial
def isParent (self parent : Name) : IR → IR → Bool
  | mk _ (.category ns), mk _ (.category np) => ns == np || (ns == self && np == parent)
  | mk _ (.atom ss), mk _ (.atom sp) => ss == sp
  | mk _ (.sepBy irs seps), mk _ (.sepBy irp sepp) => isParentSeq irs irp && seps == sepp
  | mk _ (.optional irs), mk _ (.optional irp) => isParentSeq irs irp
  | _, _ => false
where
  isParentSeq (irs irp : Array IR) :=
    (irs.zip irp).all fun (irs, irp) => isParent self parent irs irp

def _root_.Array.product (as : Array (Array α)) : Array α :=
  as.foldl (init := #[]) fun as acc => as.map (acc.push ·) |>.flatten

partial
def toIsParentMatchAlts (nameIdent isIdent : Ident) (qualified pqualified : Name) (ir pir : Array IR)
  : CommandElabM (TSyntaxArray `Lean.Parser.Term.matchAlt) := do
  if ir.size != pir.size then
    throwErrorAt nameIdent "length of child production ({ir.size}) doesn't match length of parent production ({pir.size})"

  let (argsAndOps, extraAcc) ← toArgsAndOps (ir.zip pir)
  let argsAndOps := argsAndOps ++ extraAcc.map fun (args, ops, recArgs) =>
    (args, ops.push <| mkApp isIdent #[mkApp (mkIdent <| pqualified ++ nameIdent.getId) recArgs])
  argsAndOps.mapM fun (args, ops) => do
    let lhs := mkApp (mkIdent <| pqualified ++ nameIdent.getId) args
    let rhs ← if let some op := ops[0]? then
        ops.foldlM (init := op) (start := 1) fun acc op => ``($acc && $op)
      else
        ``(true)
    `(matchAltExpr| | $lhs => $rhs)
where
  filterTypeIR (ir : Array IR) := ir.filterM fun ir => return Option.isSome <| ← IR.toType ir

  mkProd (as : Array Term) : CommandElabM Term := if let some a := as.back? then
      as.foldrM (init := a) (start := as.size - 1) fun a acc => `(($acc, $a))
    else
      ``(())

  foldlAnd (as : Array Term) : CommandElabM Term := if let some a := as[0]? then
      as.foldlM (init := a) (start := 1) fun acc a => `($acc && $a)
    else
      ``(true)

  toArgsAndOps (irs : Array (IR × IR)) (namesAcc : Array Ident := #[])
    (extraAcc : Array (Array Term × Array Term × Array Term) := #[])
    (acc : Array (Array Term × Array Term) := #[(#[], #[])])
    : CommandElabM ((Array (Array Term × Array Term)) × Array (Array Term × Array Term × Array Term)) := do
    let some (mk _ ir, mk l pir) := irs[0]? | return (acc, extraAcc)
    let irs' := irs.extract 1 irs.size

    match ir, pir with
    | .category n, .category np => do
      if n == np then
        return ← toArgsAndOps irs' (namesAcc.push l) extraAcc <|
          ← acc.mapM fun (args, ops) => return (args.push <| ← `(_), ops)

      if n == qualified && np == pqualified then
        return ← toArgsAndOps irs' (namesAcc.push l) extraAcc <|
          ← acc.mapM fun (args, ops) => return (args.push l, ops.push <| ← `($isIdent $l))

      throwErrorAt nameIdent "couldn't find parent/child relationship between {pqualified} and {qualified}"
    | .atom s, .atom sp => do
      if s != sp then
        throwErrorAt nameIdent "mismatched atoms \"{s}\" and \"{sp}\""

      toArgsAndOps irs' namesAcc extraAcc acc
    | .sepBy ir sep, .sepBy pir psep => do
      if sep != psep then
        throwErrorAt nameIdent "mismatched separators \"{sep}\" and \"{psep}\""

      if ir.size != pir.size then
        throwErrorAt nameIdent "length of child sepBy ({ir.size}) doesn't match length of parent sepBy ({pir.size})"

      match ← toArgsAndOps (ir.zip pir) with
      -- In this case, the sepBy doesn't actually contain anything stored in the datatype so we can
      -- just skip it.
      | (#[(#[], #[])], #[]) => toArgsAndOps irs' namesAcc extraAcc acc
      -- In this case, there is a list with stuff in it, but it doesn't contain anything for us to
      -- check, so we can just add an underscore pattern argument and proceed.
      | (#[(_, #[])], #[]) =>
        toArgsAndOps irs' (namesAcc.push l) extraAcc <|
          ← acc.mapM fun (args, ops) => return (args.push <| ← `(_), ops)
      | (argsAndOps, extraAcc') => do
        let remainingNames := Array.map (fun (mk l _) => l) <| ← filterTypeIR <| irs'.map Prod.snd
        let extraAcc' ← extraAcc'.mapM fun (args', ops', recArgs) => do
          let argsProd ← mkProd args'
          let recArgsProd ← mkProd recArgs
          return (
            (namesAcc : Array Term) ++ #[← ``(List.cons $argsProd $l)] ++ remainingNames,
            ops',
            (namesAcc : Array Term) ++ #[← ``(List.cons $recArgsProd $l)] ++ remainingNames
          )
        let extraAcc'' ← argsAndOps.mapM fun (args', ops') => do
          let prod ← mkProd args'
          return (
            (namesAcc : Array Term) ++ #[← ``(List.cons $prod $l)] ++ remainingNames,
            ops',
            (namesAcc : Array Term) ++ #[(l : Term)] ++ remainingNames
          )
        toArgsAndOps irs' (namesAcc.push l) (extraAcc ++ extraAcc' ++ extraAcc'') <|
          ← acc.mapM fun (args, ops) => return (args.push <| ← ``(List.nil), ops)
    | .optional ir, .optional pir => do
      if ir.size != pir.size then
        throwErrorAt nameIdent "length of child sepBy ({ir.size}) doesn't match length of parent sepBy ({pir.size})"

      match ← toArgsAndOps (ir.zip pir) with
      -- In this case, the sepBy doesn't actually contain anything stored in the datatype so we can
      -- just skip it.
      | (#[(#[], #[])], #[]) => toArgsAndOps irs' namesAcc extraAcc acc
      -- In this case, there is a list with stuff in it, but it doesn't contain anything for us to
      -- check, so we can just add an underscore pattern argument and proceed.
      | (#[(_, #[])], #[]) =>
        toArgsAndOps irs' (namesAcc.push l) extraAcc <|
          ← acc.mapM fun (args, ops) => return (args.push <| ← `(_), ops)
      | (argsAndOps, extraAcc') => do
        if !extraAcc'.isEmpty then
          throwErrorAt nameIdent "sepBy inside optional of value parent is not yet supported"

        let noneAcc ← acc.mapM fun (args, ops) => return (args.push <| ← ``(Option.none), ops)
        let someAcc ← acc.concatMapM fun (args, ops) =>
          argsAndOps.mapM fun (args', ops') => do
            let prod ← mkProd args'
            return (args.push <| ← ``(Option.some $prod), ops ++ ops')
        toArgsAndOps irs' (namesAcc.push l) extraAcc <| noneAcc ++ someAcc
    | _, _ => throwErrorAt nameIdent "mismatched syntax"

end IR

end Lott.DSL
