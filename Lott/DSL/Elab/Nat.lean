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
  | `($i:ident) => Term.elabTerm i <| .some (.const `Nat [])
  | `($n:num) => Term.elabTerm n <| .some (.const `Nat [])
  | `(($t:term)) => Term.elabTerm t <| .some (.const `Nat [])
  | _ => throwUnsupportedSyntax

@[lott_tex_elab Lott.Symbol.Nat]
def natTexElab : TexElab
  | _, `($i:ident) => return texEscape <| i.getId.toString (escape := false)
  | _, `($n:num) => return texEscape <| toString n.getNat
  | _, `(($t:term)) => do
    let some ss := t.raw.getSubstring? | throwUnsupportedSyntax
    return texEscape ss.toString
  | _, _ => throwUnsupportedSyntax

end Lott.DSL.Elab
