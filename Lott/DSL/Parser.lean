import Lean.Parser

namespace Lott.DSL

open Lean
open Lean.Parser
open Lean.Parser.Syntax

/- Common trailing syntax. -/

declare_syntax_cat Lott.Trailing

-- TODO: Figure out how to be able to use underscore for separator.
syntax "▁" sepBy1(ident, "▁") : Lott.Trailing

/- Metavariable syntax. -/

syntax "metavar " ident,+ : command

/- Non-terminal syntax. -/

declare_syntax_cat Lott.DSL.DesugarConfig
declare_syntax_cat Lott.DSL.ElabConfig
declare_syntax_cat Lott.DSL.Production
declare_syntax_cat Lott.DSL.NonTerminal

syntax "(" "desugar" " := " term ")" : Lott.DSL.DesugarConfig

syntax "(" "elab" " := " term ")" : Lott.DSL.ElabConfig

syntax " | " (atom <|> ident)* " : " ident atomic(Lott.DSL.DesugarConfig)? (Lott.DSL.ElabConfig)? : Lott.DSL.Production

syntax "nonterminal " ident,+ " := " Lott.DSL.Production* : Lott.DSL.NonTerminal

syntax Lott.DSL.NonTerminal : command

/- Judgement syntax. -/

declare_syntax_cat Lott.Judgement
declare_syntax_cat Lott.DSL.InferenceRule
declare_syntax_cat Lott.DSL.JudgementDecl

syntax "judgement_syntax " (atom <|> ident)* " : " ident : command

syntax Lott.Judgement* "─"+ ident Lott.Judgement : Lott.DSL.InferenceRule

syntax "judgement " ident " := " Lott.DSL.InferenceRule* : Lott.DSL.JudgementDecl

syntax Lott.DSL.JudgementDecl : command

/- Term embedding syntax. -/

-- Mostly copied from Lean/Parser/Extension.lean, Lean/PrettyPrinter/Formatter.lean, and
-- Lean/PrettyPrinter/Parenthesizer.lean, but with a prefix automatically added to the name.
private
def parserOfStackFn (offset : Nat) : ParserFn := fun c s => Id.run do
  let stack := s.stxStack
  if stack.size < offset + 1 then
    return s.mkUnexpectedError "failed to determine parser using syntax stack, stack is too small"
  let .ident _ _ parserName _ := stack.get! (stack.size - offset - 1)
    | s.mkUnexpectedError "failed to determine parser using syntax stack, the specified element on the stack is not an identifier"
  let parserName := mkIdent <| `Lott.Symbol ++ parserName
  let oldStackSize := s.stackSize
  let s ← match c.resolveParserName ⟨parserName⟩ with
    | [.category cat] => categoryParserFn cat c s
    | [_] => return s.mkUnexpectedError s!"parser name {parserName} should be a lott symbol category, not a parser or alias"
    | _ :: _ :: _ => return s.mkUnexpectedError s!"ambiguous parser name {parserName}"
    | [] => return s.mkUnexpectedError s!"unknown parser {parserName}"
  if !s.hasError && s.stackSize != oldStackSize + 1 then
    return s.mkUnexpectedError "expected parser to return exactly one syntax object"
  s

private
def parserOfStack (offset : Nat) (prec : Nat := 0) : Parser where
  fn := adaptCacheableContextFn ({ · with prec }) (parserOfStackFn offset)

open PrettyPrinter Formatter in
@[combinator_formatter parserOfStack]
private
def parserOfStack.formatter (offset : Nat) (_prec : Nat := 0) : Formatter := do
  let st ← get
  let stx := st.stxTrav.parents.back.getArg (st.stxTrav.idxs.back - offset)
  formatterForKind stx.getKind

open PrettyPrinter Parenthesizer in
@[combinator_parenthesizer parserOfStack]
private
def parserOfStack.parenthesizer (offset : Nat) (_prec : Nat := 0) : Parenthesizer := do
  let st ← get
  let stx := st.stxTrav.parents.back.getArg (st.stxTrav.idxs.back - offset)
  parenthesizerForKind stx.getKind

private
def lottSymbolParser := incQuotDepth (parserOfStack 1)

syntax (name := lott_symbol_embed) "[[" ident "|" lottSymbolParser "]]" : term

syntax "[[" Lott.Judgement "]]" : term

end Lott.DSL
