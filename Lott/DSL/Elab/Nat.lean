import Lott.DSL.Elab

namespace Lott.DSL.Elab

open Lean
open Lean.Elab
open Lean.Parser

declare_syntax_cat Lott.Symbol.Nat

run_cmd setEnv <| symbolExt.addEntry (← getEnv) { canon := `Nat, alias := `n }

@[Lott.Symbol.Nat_parser]
def nat.n_parser : Parser := leadingNode `Lott.Symbol.Nat maxPrec <| identPrefix "n"

@[Lott.Symbol.Nat_parser]
def nat.num_parser : Parser := leadingNode `Lott.Symbol.Nat maxPrec numLit

@[Lott.Symbol.Nat_parser]
def nat.term_parser : Parser :=
  leadingNode `Lott.Symbol.Nat maxPrec <| "(" >> checkLineEq >> termParser >> checkLineEq >> ")"

@[lott_term_elab Lott.Symbol.Nat]
def natTermElab : TermElab
  | .node _ `Lott.Symbol.Nat #[n@(.ident ..)]
  | .node _ `Lott.Symbol.Nat #[n@(.node _ `num _)]
  | .node _ `Lott.Symbol.Nat #[.atom _ "(", n, .atom _ ")"] =>
    Term.elabTerm n <| .some (.const `Nat [])
  | _ => throwUnsupportedSyntax

@[lott_tex_elab Lott.Symbol.Nat]
def natTexElab : TexElab
  | _, Syntax.node _ `Lott.Symbol.Nat #[i@(.ident ..)] =>
    return texEscape <| i.getId.toString (escape := false)
  | _, .node _ `Lott.Symbol.Nat #[s@(.node _ `num _)]
  | _, .node _ `Lott.Symbol.Nat #[.atom _ "(", s, .atom _ ")"] => do
    let some ss := s.getSubstring? | throwUnsupportedSyntax
    return texEscape ss.toString
  | _, _ => throwUnsupportedSyntax

end Lott.DSL.Elab
