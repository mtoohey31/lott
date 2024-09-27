import Lean

namespace Lott.DSL

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Syntax
open Lean.Parser
open Lean.Parser.Command
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
def toIsChildCtor (prodIdent isIdent : Ident) (qualified pqualified : Name) (ir pir : Array IR)
  : CommandElabM (TSyntax `Lean.Parser.Command.ctor) := do
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
  toTerms (as : TSyntaxArray `Lean.binderIdent) : CommandElabM (Array Term) :=
    as.mapM fun
      | `(Lean.binderIdent| $h:hole) => `(term| $h:hole)
      | `(Lean.binderIdent| $i:ident) => `(term| $i:ident)
      | _ => throwUnsupportedSyntax

  foldrArrow (args : Array Term) (init : Term) : CommandElabM Term :=
    args.foldrM (init := init) fun arg acc => ``($arg → $acc)

  foldrProd (as : Array Term) : CommandElabM Term := if let some a := as.back? then
      as.foldrM (init := a) (start := as.size - 1) fun a acc => `(($acc, $a))
    else
      ``(())

  foldlAnd (as : Array Term) : CommandElabM Term := if let some a := as[0]? then
      as.foldlM (init := a) (start := 1) fun acc a => `($acc ∧ $a)
    else
      ``(True)

  go (irs : Array (IR × IR)) (patAcc : TSyntaxArray `Lean.binderIdent := #[])
    (propAcc : Array Term := #[])
    : CommandElabM (TSyntaxArray `Lean.binderIdent × Array Term) := do
    let some (mk l' ir, mk l pir) := irs[0]? | return (patAcc, propAcc)
    let irs' := irs.extract 1 irs.size

    let lbi ← `(Lean.binderIdent| $l:ident)
    let l'bi ← `(Lean.binderIdent| $l':ident)
    let hole ← `(Lean.binderIdent| _)

    match ir, pir with
    | .category n, .category np => do
      if n == np then
        return ← go irs' (patAcc.push hole) propAcc

      if n == qualified && np == pqualified then
        return ← go irs' (patAcc.push lbi) <| propAcc.push <| ← `($isIdent $l)

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
      -- In this case, the optional doesn't actually contain anything stored in the datatype so we can
      -- just skip it.
      | (#[], #[]) => go irs' patAcc propAcc
      -- In this case, there is a list with stuff in it, but it doesn't contain anything for us to
      -- check, so we can just add an underscore pattern argument and proceed.
      | (_, #[]) => go irs' (patAcc.push hole) propAcc
      | (#[patArg], props) => go irs' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $patArg:binderIdent ∈ $l, $(← foldlAnd props))
      | (patArgs, props) => go irs' (patAcc.push lbi) <| propAcc.push <| ←
          ``(∀ $l'bi ∈ $l, let $(← foldrProd <| ← toTerms patArgs):term := $l'; $(← foldlAnd props))
    | _, _ => throwErrorAt prodIdent "mismatched syntax"

end IR

end Lott.DSL
