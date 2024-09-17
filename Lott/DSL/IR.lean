import Lean

namespace Lott.DSL

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Syntax
open Lean.Parser
open Lean.Parser.Term

def symbolPrefix := `Lott.Symbol

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

private partial
def splitTrailing (ir : Array IR) (catName : Name) : Option (CommandElabM (Array IR)) := do
  match (← ir[0]?) with
  | mk _ (.category n) =>
    if symbolPrefix ++ n == catName then
      return return ir.extract 1 ir.size
    else
      none
  | mk _ (.atom _) => none
  -- TODO: Support trailing nested inside of sepBy1 and optional.
  | mk _ (.sepBy ir' _)
  | mk _ (.optional ir') => do
    let _ ← IR.splitTrailing ir' catName
    return throwUnsupportedSyntax

mutual
private partial
def toParser' : IR → CommandElabM Term
  | mk _ (.category n) => ``(categoryParser $(quote <| symbolPrefix ++ n) Parser.maxPrec)
  | mk _ (.atom s) => ``(symbol $(mkStrLit s))
  | mk _ (.sepBy ir sep) => do ``(sepBy $(← toParserSeq ir) $(quote sep))
  | mk _ (.optional ir) => do ``(Parser.optional $(← toParserSeq ir))

private partial
def toParserSeq (ir : Array IR) : CommandElabM Term := do
  if ir.size == 0 then
    throwUnsupportedSyntax

  ir.extract 1 ir.size |>.foldlM (init := ← ir[0]!.toParser')
    fun acc ir => do ``($acc >> checkLineEq >> $(← ir.toParser'))
end

def toParser (ir : Array IR) (catName : Name) : CommandElabM (Term × Term) := do
  if let some ir' := IR.splitTrailing ir catName then
    let rest ← toParserSeq (← ir')
    return (
      ← ``(trailingNode $(quote catName) Parser.maxPrec 0 <| checkLineEq >> $rest),
      ← ``(TrailingParser),
    )
  else
    let rest ← toParserSeq ir
    return (← ``(leadingNode $(quote catName) Parser.maxPrec $rest), ← ``(Parser))

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
  return some <| ← types.extract 1 types.size |>.foldlM (init := type') fun acc t => ``($acc × $t)
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
  types.extract 0 (types.size - 1) |>.foldrM (β := Term) (init := back) fun t acc =>
    ``(mkApp2 (Expr.const `Prod [levelOne, levelOne]) $t $acc)
end

def toTypeArrSeq (ir : Array IR) (init : Term) : CommandElabM Term := do
  (← ir.filterMapM IR.toType) |>.foldrM (init := init) fun t acc => ``($t → $acc)

private
def toPatternArg : IR → CommandElabM (TSyntax `term)
  | mk l (.category n) => `($l@(Lean.Syntax.node _ $(quote <| symbolPrefix ++ n) _))
  | mk l (.atom s) => `($l@(Lean.Syntax.atom _ $(quote s.trim)))
  | mk l (.sepBy ..) => `($l@(Lean.Syntax.node _ `null _))
  | mk l (.optional ..) => `($l@(Lean.Syntax.node _ `null _))

def toPatternArgs (ir : Array IR) : CommandElabM (TSepArray `term ",") :=
  ir.mapM IR.toPatternArg

def toJoinArgs (ir : Array IR) : TSepArray `term "," :=
  ir.map (β := TSyntax `term) fun | mk l _ => l

end IR

end Lott.DSL
