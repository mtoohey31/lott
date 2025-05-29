import Lott.Parser

namespace Lott

open Lean.Parser

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
      (orelseFn
        (atomicFn (andthenFn qualifiedSymbolParser.fn embedCloseFn))
        (atomicFn (andthenFn (withPosition (categoryParser `Lott.Symbol 0)).fn embedCloseFn)))
      (andthenFn (withPosition (categoryParser `Lott.Judgement 0)).fn embedCloseFn) c s
    if s.hasError then
      s
    else
      filterParserFnAux s.pos c s
  else
    filterParserFnAux startPos c <| s.next' c.input s.pos h

def filterParserFn : ParserFn := fun c s => filterParserFnAux s.pos c s

def inputParserFn : ParserFn := orelseFn
  (orelseFn
    (atomicFn (andthenFn qualifiedSymbolParser.fn whitespace))
    (atomicFn (andthenFn (withPosition (categoryParser `Lott.Judgement 0)).fn whitespace)))
  (andthenFn (withPosition (categoryParser `Lott.Symbol 0)).fn whitespace)

syntax "#filter " str (str)? : command

end Lott
