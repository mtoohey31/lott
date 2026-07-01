module

meta import Lott.Parser

meta section

namespace Lott

open Lean.Parser

def embedCloseFn : ParserFn := fun c s =>
  let p := s.pos
  if h : c.atEnd p then
    s.mkUnexpectedErrorAt "expected ']]'" p
  else if c.get' p h == ']' then
    let s := s.next' c p h
    if h : c.atEnd s.pos then
      s.mkUnexpectedErrorAt "expected ']]'" p
    else if c.get' s.pos h == ']' then
      s.next' c s.pos h
    else
      s.mkUnexpectedErrorAt "expected ']]'" p
  else
    s.mkUnexpectedErrorAt "expected ']]'" p

partial
def filterParserFnAux (startPos : String.Pos.Raw) : ParserFn := fun c s =>
  let p := s.pos
  if h : c.atEnd p then
    (mkNodeToken `Lott.NonEmbed startPos) c s
  else if c.get' p h = '[' then
    let s' := s.next' c p h
    if h : c.atEnd s'.pos then
      filterParserFnAux startPos c s'
    else if c.get' s'.pos h == '[' then
      let s := s'.next' c s'.pos h
      let s := (mkNodeToken `Lott.NonEmbed startPos) c s
      let s := orelseFn
        (orelseFn
          (atomicFn (andthenFn qualifiedSymbolParser.fn embedCloseFn))
          (atomicFn (andthenFn (withPosition (categoryParser `Lott.Symbol 0)).fn embedCloseFn)))
        (andthenFn (withPosition (categoryParser `Lott.Judgement 0)).fn embedCloseFn) c s
      if s.hasError then
        s
      else
        filterParserFnAux p c s
    else
      filterParserFnAux startPos c s'
  else
    filterParserFnAux startPos c <| s.next' c p h

def filterParserFn : ParserFn := fun c s => filterParserFnAux s.pos c s

def inputParserFn : ParserFn := orelseFn
  (orelseFn
    (atomicFn (andthenFn qualifiedSymbolParser.fn whitespace))
    (atomicFn (andthenFn (withPosition (categoryParser `Lott.Judgement 0)).fn whitespace)))
  (andthenFn (withPosition (categoryParser `Lott.Symbol 0)).fn whitespace)

syntax "#filter " str (str)? : command

end Lott
