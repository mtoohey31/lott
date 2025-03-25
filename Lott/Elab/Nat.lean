import Lott.Elab

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
      private
      def $parserIdent : Parser :=
        leadingNode `Lott.Symbol.Nat maxPrec <| identPrefix $(quote <| alias.toString))

run_cmd addNatAlias `n

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

@[lott_tex_elab Lott.Symbol.Nat]
private
def natTexElab : TexElab
  | _, .node _ `Lott.Symbol.Nat #[n@(.ident ..)]
  | _, .node _ `Lott.Symbol.Nat #[n@(.node _ `num _)] => texElabIdx n
  | _, .node _ `Lott.Symbol.Nat #[.atom _ "(", n, .atom _ ")"] => do
    let some n := n.getSubstring? (withLeading := false) (withTrailing := false)
      | throwUnsupportedSyntax
    return s!"({n.toString.texEscape})"
  | _, _ => throwUnsupportedSyntax

end Lott
