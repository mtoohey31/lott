import Lott.Elab

namespace Lott.Elab

open Lean
open Lean.Elab
open Lean.Parser

declare_syntax_cat Lott.Symbol.Nat

run_cmd setEnv <| aliasExt.addEntry (← getEnv) { canon := `Nat, alias := `n }

@[Lott.Symbol.Nat_parser]
def nat.n_parser : Parser := leadingNode `Lott.Symbol.Nat maxPrec <| identPrefix "n"

@[Lott.Symbol.Nat_parser]
def nat.num_parser : Parser := leadingNode `Lott.Symbol.Nat maxPrec numLit

@[Lott.Symbol.Nat_parser]
def nat.term_parser : Parser :=
  leadingNode `Lott.Symbol.Nat maxPrec <| "(" >> checkLineEq >> termParser >> checkLineEq >> ")"

@[lott_term_elab Lott.Symbol.Nat]
def natTermElab : TermElab
  | _, .node _ `Lott.Symbol.Nat #[n@(.ident ..)]
  | _, .node _ `Lott.Symbol.Nat #[n@(.node _ `num _)]
  | _, .node _ `Lott.Symbol.Nat #[.atom _ "(", n, .atom _ ")"] =>
    Term.elabTerm n <| .some (.const `Nat [])
  | _, _ => throwUnsupportedSyntax

end Lott.Elab
