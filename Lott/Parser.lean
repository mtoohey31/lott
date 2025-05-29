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

def texPrePostConfig :=
  "(" >> nonReservedSymbol "tex " >> nonReservedSymbol "pre" >> " := " >> strLit >> ", " >>
    nonReservedSymbol "post" >> " := " >> strLit >> ") "

syntax "locally_nameless "? "metavar " (texPrePostConfig)? ident,+ : command

/- Non-terminal syntax. -/

declare_syntax_cat Lott.Symbol
declare_syntax_cat Lott.Production
declare_syntax_cat Lott.NonTerminal

def prodArg := leading_parser
  Parser.optional (atomic (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> syntaxParser argPrec

def bindConfig :=
  " (" >> nonReservedSymbol "bind " >> ident >> optional (" in " >> sepBy1 ident ", ") >> ")"

def idConfig := " (" >> nonReservedSymbol "id " >> sepBy1 ident ", " >> ")"

def expandConfig := " (" >> nonReservedSymbol "expand" >> " := " >> termParser >> ")"

def texConfig := " (" >> nonReservedSymbol "tex" >> optional ident >> " := " >> termParser >> ")"

def strLitTexConfig := " (" >> nonReservedSymbol "tex" >> " := " >> strLit >> ")"

syntax ppLine "|" (ppSpace prodArg)+ " : " withPosition(ident (lineEq " nosubst")? " notex"?) atomic(bindConfig)? atomic(idConfig)? atomic(expandConfig)? (texConfig)* : Lott.Production

private
def parent := nonReservedSymbol "parent"

syntax "nosubst "? "nonterminal " atomic("(" parent " := " ident ") ")? (texPrePostConfig)? (ident " notex"? (strLitTexConfig)?),+ " := " Lott.Production* : Lott.NonTerminal

syntax Lott.NonTerminal : command

/- Judgement syntax. -/

declare_syntax_cat Lott.Judgement
declare_syntax_cat Lott.InferenceRuleUpper
declare_syntax_cat Lott.InferenceRule
declare_syntax_cat Lott.JudgementDeclRHS
declare_syntax_cat Lott.JudgementDecl

syntax "judgement_syntax" (ppSpace stx)+ " : " ident atomic(idConfig)? (texConfig)* : command

private
def bracketedBinder := Term.bracketedBinder

syntax Lott.Judgement : Lott.InferenceRuleUpper

syntax ident " := " Lott.Symbol : Lott.InferenceRuleUpper

syntax "notex " ("for " ident)? Lott.InferenceRuleUpper : Lott.InferenceRuleUpper

def commentConfig :=
  " (" >> nonReservedSymbol "comment" >> optional ident >> optional (" := " >> strLit) >> ")"

syntax withPosition(ppLine Lott.InferenceRuleUpper)* ppLine "─"+ withPosition(ident atomic(lineEq commentConfig)* (lineEq bracketedBinder)* (lineEq " notex")?) withPosition(ppLine Lott.Judgement) : Lott.InferenceRule

syntax " where" ppLine Lott.InferenceRule* : Lott.JudgementDeclRHS

syntax " := " term : Lott.JudgementDeclRHS

syntax "judgement " ident Lott.JudgementDeclRHS : Lott.JudgementDecl

syntax Lott.JudgementDecl : command

syntax (name := zetaReduce) "zeta_reduce% " term : term

/- Conditional syntax. -/

syntax "termonly " command : command

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
    | s.mkUnexpectedError s!"failed to determine parser using syntax stack, the specified element on the stack is not an identifier: {stack.get! (stack.size - offset)} {stack.get! (stack.size - offset - 1)} {stack.get! (stack.size - offset - 2)} {stack.get! (stack.size - offset - 3)}"
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

def qualifiedSymbolParser := leadingNode `Lott.QualifiedSymbol Parser.maxPrec <|
  ident >> "| " >> incQuotDepth (parserOfStack 1)

@[term_parser]
def qualifiedSymbolEmbed := leading_parser
  "[[" >> qualifiedSymbolParser >> "]]"

/- External interaction syntax. -/

private
def embedCloseFn : ParserFn := fun c s =>
  if c.input.substrEq s.pos "]]" 0 2 then
    s.setPos <| s.pos + "]]".endPos
  else
    s.mkUnexpectedErrorAt "expected ']]'" s.pos

private partial
def filterParserFnAux (startPos : String.Pos) : ParserFn := fun c s =>
  if h : c.input.atEnd s.pos then
    mkNodeToken `Lott.NonEmbed startPos c s
  else if c.input.substrEq s.pos "[[" 0 2 then
    let s := mkNodeToken `Lott.NonEmbed startPos c s
    let s := s.setPos <| s.pos + "[[".endPos
    let s := orelseFn
      (atomicFn (andthenFn (withPosition (categoryParser `Lott.Symbol 0)).fn embedCloseFn))
      (andthenFn (withPosition (categoryParser `Lott.Judgement 0)).fn embedCloseFn) c s
    if s.hasError then
      s
    else
      filterParserFnAux s.pos c s
  else
    filterParserFnAux startPos c <| s.next' c.input s.pos h

def filterParserFn : ParserFn := fun c s => filterParserFnAux s.pos c s

syntax "#filter " str (str)? : command

end Lott
