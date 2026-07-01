module

public import Lean.Elab.Command
public meta import Lott.Data.String
public import Lott.Elab.Basic
import all Lott.Elab.Basic
import all Lott.Environment.Basic
public import Lott.Parser

meta section

namespace Lott

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Parser

declare_syntax_cat Lott.Symbol.Nat

def addNatAlias (alias : Name) : CommandElabM Unit := do
  setEnv <| aliasExt.addEntry (← getEnv) { canon := `Nat, alias, tex? := none }
  let parserIdent := mkIdent <| `nat ++ (alias.appendAfter "_parser")
  elabCommand <| ←
    `(@[Lott.Symbol.Nat_parser]
      public
      def $parserIdent : Parser :=
        leadingNode `Lott.Symbol.Nat maxPrec <| identPrefix $(quote <| alias.toString))

run_cmd addNatAlias `n

public section

@[Lott.Symbol.Nat_parser]
def nat.num_parser : Parser := leadingNode `Lott.Symbol.Nat maxPrec numLit

@[Lott.Symbol.Nat_parser]
def nat.term_parser : Parser :=
  leadingNode `Lott.Symbol.Nat maxPrec <| "{{" >> checkLineEq >> termParser >> checkLineEq >> "}}"

@[macro symbolEmbed]
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
      .node _ `Lott.Symbol.Nat #[.atom _ "{{", n, .atom _ "}}"],
      .atom _ "]]"
    ] => return n
  | _ => Macro.throwUnsupported

@[lott_tex_elab Lott.Symbol.Nat]
def natTexElab : TexElab
  | _, _, .node _ `Lott.Symbol.Nat #[n@(.ident ..)]
  | _, _, .node _ `Lott.Symbol.Nat #[n@(.node _ `num _)] => texElabIdx n
  | _, _, .node _ `Lott.Symbol.Nat #[.atom _ "{{", n, .atom _ "}}"] => do
    let some n := n.getSubstring? (withLeading := false) (withTrailing := false)
      | throwUnsupportedSyntax
    return s!"({n.toString.texEscape})"
  | _, _, _ => throwUnsupportedSyntax

end

end Lott
