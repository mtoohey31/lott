import Lean.Parser

namespace Lott

open Lean
open Lean.Parser
open Lean.Parser.Syntax

/- Common trailing syntax. -/

declare_syntax_cat Lott.Trailing

def isPrefixOf (prefix' : String) (n : Name) : Bool := prefix'.isPrefixOf n.getRoot.getString!

def identPrefixFn (prefix' : String) : ParserFn := fun c s =>
  let s := tokenFn ["identifier"] c s
  if s.hasError then
    s
  else
    match s.stxStack.back with
    | .ident _ _ val _ =>
      if !isPrefixOf prefix' val then
        s.mkUnexpectedTokenError s!"identifier beginning with '{prefix'}'"
      else
        s
    | _ => s.mkUnexpectedTokenError "identifier"

def identPrefix (prefix' : String) : Parser := {
  fn := identPrefixFn prefix'
  info := mkAtomicInfo "ident"
}

@[combinator_parenthesizer identPrefix] def identPrefix.parenthesizer (_prefix : String) :=
  PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter identPrefix] def identPrefix.formatter (_parser : String) :=
  PrettyPrinter.Formatter.rawIdentNoAntiquot.formatter

/- Metavariable syntax. -/

syntax "locally_nameless"? "metavar " ident,+ : command

/- Non-terminal syntax. -/

declare_syntax_cat Lott.Symbol
declare_syntax_cat Lott.BindConfig
declare_syntax_cat Lott.IdConfig
declare_syntax_cat Lott.DesugarConfig
declare_syntax_cat Lott.ElabConfig
declare_syntax_cat Lott.Production
declare_syntax_cat Lott.NonTerminal

private
def bind := nonReservedSymbol "bind"

syntax "(" bind ident (" in " ident,+)? ")" : Lott.BindConfig

private
def id := nonReservedSymbol "id"

syntax "(" id ident,+ ")" : Lott.IdConfig

private
def desugar := nonReservedSymbol "desugar"

syntax "(" desugar " := " term ")" : Lott.DesugarConfig

syntax "(" "elab" " := " term ")" : Lott.ElabConfig

def prodArg  := leading_parser
  Parser.optional (atomic (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> syntaxParser argPrec

syntax " | " prodArg+ " : " withPosition(ident (lineEq "nosubst")?) atomic(Lott.BindConfig)? atomic(Lott.IdConfig)? atomic(Lott.DesugarConfig)? (Lott.ElabConfig)? : Lott.Production

syntax "nosubst"? "nonterminal " ("(" "parent" " := " ident ")")? ident,+ " := " Lott.Production* : Lott.NonTerminal

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

syntax (name := lott_symbol_embed) "[[" ident "|" lottSymbolParser "]]" : term

syntax "[[" withPosition(Lott.Symbol) "]]" : term

syntax "[[" withPosition(Lott.Judgement) "]]" : term

/- External interaction syntax. -/

partial
def filterParserFnAux (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  let i := s.pos
  if h : input.atEnd i then
    mkNodeToken `Lott.NonEmbed startPos c s
  else if input.get i == '[' then
    let s' := s.next' input i h
    let i' := s'.pos
    if h' : input.atEnd i' then
      mkNodeToken `Lott.NonEmbed startPos c s'
    else if input.get i' == '[' then
      let val := input.extract startPos i
      let leading := mkEmptySubstringAt input startPos
      let trailing := mkEmptySubstringAt input i
      let info := SourceInfo.original leading startPos trailing i
      let s'' := s'.pushSyntax (Syntax.mkLit `Lott.NonEmbed val info) |>.next' input i' h'
      let s''' := whitespace c s''
      if s'''.hasError then
        s'''
      else
        let s'''' := withPosition (orelse
          (categoryParser `Lott.Symbol 0)
          (categoryParser `Lott.Judgement 0)) |>.fn c s'''
        if s''''.hasError then
          s''''
        else
          let s''''' := whitespace c s''''
          let i''''' := s'''''.pos
          if h''''' : input.atEnd i''''' then
            s'''''.mkEOIError
          else if input.get i''''' == ']' then
            let s'''''' := s'''''.next' input i''''' h'''''
            let i'''''' := s''''''.pos
            if h'''''' : input.atEnd i'''''' then
              s''''''.mkEOIError
            else if input.get i'''''' == ']' then
              let s''''''' := s''''''.next' input i'''''' h''''''
              filterParserFnAux s'''''''.pos c s'''''''
            else
              s''''''.mkErrorAt "expected ']]'" i''''''
          else
            s'''''.mkErrorAt "expected ']]'" i'''''
    else
      filterParserFnAux startPos c <| s'.next' input i' h'
  else
    filterParserFnAux startPos c <| s.next' input i h

def filterParserFn : ParserFn := fun c s => filterParserFnAux s.pos c s

def filterParser : Parser := { fn := filterParserFn }

syntax "filter " str str : command

end Lott
