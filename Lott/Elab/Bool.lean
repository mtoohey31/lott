import Lott.Elab

namespace Lott

open Lean
open Lean.Elab
open Lean.Parser

declare_syntax_cat Lott.Symbol.Bool

run_cmd setEnv <| aliasExt.addEntry (← getEnv) { canon := `Bool, alias := `b, tex? := none }

@[Lott.Symbol.Bool_parser]
private
def bool.b_parser : Parser := leadingNode `Lott.Symbol.Bool maxPrec <| identPrefix "b"

@[macro symbolEmbed]
private
def boolImpl : Macro := fun stx => do
  let .node _ `Lott.symbolEmbed #[
    .atom _ "[[",
    .node _ `Lott.Symbol.Bool #[b@(.ident ..)],
    .atom _ "]]"
  ] := stx | Macro.throwUnsupported
  return b

end Lott
