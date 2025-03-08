import Lott.Elab

namespace Lott.Elab

open Lean
open Lean.Elab
open Lean.Parser

declare_syntax_cat Lott.Symbol.Bool

run_cmd setEnv <| aliasExt.addEntry (← getEnv) { canon := `Bool, alias := `b }

@[Lott.Symbol.Bool_parser]
def bool.b_parser : Parser := leadingNode `Lott.Symbol.Bool maxPrec <| identPrefix "b"

@[lott_term_elab Lott.Symbol.Bool]
def boolTermElab : TermElab
  | _, .node _ `Lott.Symbol.Bool #[n@(.ident ..)] =>
    Term.elabTerm n <| .some (.const `Bool [])
  | _, _ => throwUnsupportedSyntax

end Lott.Elab
