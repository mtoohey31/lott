import Lott.Elab

namespace Lott

open Lean
open Lean.Elab
open Lean.Parser

declare_syntax_cat Lott.Symbol.Nat

run_cmd setEnv <| aliasExt.addEntry (← getEnv) { canon := `Nat, alias := `n }

@[Lott.Symbol.Nat_parser]
private
def nat.n_parser : Parser := leadingNode `Lott.Symbol.Nat maxPrec <| identPrefix "n"

@[Lott.Symbol.Nat_parser]
private
def nat.num_parser : Parser := leadingNode `Lott.Symbol.Nat maxPrec numLit

@[Lott.Symbol.Nat_parser]
private
def nat.term_parser : Parser :=
  leadingNode `Lott.Symbol.Nat maxPrec <| "(" >> checkLineEq >> termParser >> checkLineEq >> ")"

@[macro symbolEmbed]
private
def natImpl : Macro
  | .node _ `Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ `Lott.Symbol.Nat #[n@(.ident ..)],
      .atom _ "]]"
    ]
  | .node _ `Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ `Lott.Symbol.Nat #[n@(.node _ `num _)],
      .atom _ "]]"
    ]
  | .node _ `Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ `Lott.Symbol.Nat #[.atom _ "(", n, .atom _ ")"],
      .atom _ "]]"
    ] => return n
  | _ => Macro.throwUnsupported

end Lott
