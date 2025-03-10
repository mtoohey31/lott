import Lean.Elab
import Lean.Parser

namespace Lott

open Lean
open Lean.Parser
open Lean.Parser.Syntax

/- Common trailing syntax. -/

private
def identPrefixFn («prefix» : String) : ParserFn := fun c s =>
  let s := tokenFn ["identifier"] c s
  if s.hasError then
    s
  else
    match s.stxStack.back with
    | .ident _ _ val _ =>
      if !prefix.isPrefixOf val.getRoot.getString! then
        s.mkUnexpectedTokenError s!"identifier beginning with '{«prefix»}'"
      else
        s
    | _ => s.mkUnexpectedTokenError "identifier"

def identPrefix («prefix» : String) : Parser where
  fn := identPrefixFn «prefix»
  info := mkAtomicInfo "ident"

@[combinator_parenthesizer identPrefix]
def identPrefix.parenthesizer (_ : String) :=
  PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter identPrefix]
def identPrefix.formatter (_ : String) :=
  PrettyPrinter.Formatter.rawIdentNoAntiquot.formatter

/- Metavariable syntax. -/

syntax "locally_nameless"? "metavar " ident,+ : command

/- Non-terminal syntax. -/

declare_syntax_cat Lott.Symbol
declare_syntax_cat Lott.BindConfig
declare_syntax_cat Lott.IdConfig
declare_syntax_cat Lott.ExpandConfig
declare_syntax_cat Lott.Production
declare_syntax_cat Lott.NonTerminal

private
def bind := nonReservedSymbol "bind"

syntax "(" bind ident (" in " ident,+)? ")" : Lott.BindConfig

private
def id := nonReservedSymbol "id"

syntax "(" id ident,+ ")" : Lott.IdConfig

private
def expand := nonReservedSymbol "expand"

syntax "(" expand " := " term ")" : Lott.ExpandConfig

def prodArg  := leading_parser
  Parser.optional (atomic (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> syntaxParser argPrec

syntax " | " prodArg+ " : " withPosition(ident (lineEq "nosubst")?) atomic(Lott.BindConfig)? atomic(Lott.IdConfig)? (Lott.ExpandConfig)? : Lott.Production

private
def parent := nonReservedSymbol "parent"

syntax "nosubst"? "nonterminal " ("(" parent " := " ident ")")? ident,+ " := " Lott.Production* : Lott.NonTerminal

syntax Lott.NonTerminal : command

/- Judgement syntax. -/

declare_syntax_cat Lott.Judgement
declare_syntax_cat Lott.InferenceRule
declare_syntax_cat Lott.JudgementDecl

syntax "judgement_syntax " stx+ " : " ident (Lott.IdConfig)? : command

private
def bracketedBinder := Term.bracketedBinder

syntax withPosition(Lott.Judgement)* "─"+ withPosition(ident (lineEq bracketedBinder)*) withPosition(Lott.Judgement) : Lott.InferenceRule

syntax "judgement " ident " := " Lott.InferenceRule* : Lott.JudgementDecl

syntax Lott.JudgementDecl : command

/- Term embedding syntax. -/

syntax (name := symbolEmbed) "[[" withPosition(Lott.Symbol) "]]" : term

syntax (name := judgementEmbed) "[[" withPosition(Lott.Judgement) "]]" : term

/-
Like Lean/Parser/Extension.lean, Lean/PrettyPrinter/Formatter.lean, and
Lean/PrettyPrinter/Parenthesizer.lean, but with the Lott.Symbol prefix automatically added.
-/
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
  let stx := st.stxTrav.parents.back!.getArg (st.stxTrav.idxs.back! - offset)
  formatterForKind stx.getKind

open PrettyPrinter Parenthesizer in
@[combinator_parenthesizer parserOfStack]
private
def parserOfStack.parenthesizer (offset : Nat) (_prec : Nat := 0) : Parenthesizer := do
  let st ← get
  let stx := st.stxTrav.parents.back!.getArg (st.stxTrav.idxs.back! - offset)
  parenthesizerForKind stx.getKind

private
def lottSymbolParser := incQuotDepth (parserOfStack 1)

macro "[[" ident "|" symbol:lottSymbolParser "]]" : term => `([[$(.mk symbol.raw):Lott.Symbol]])

end Lott
