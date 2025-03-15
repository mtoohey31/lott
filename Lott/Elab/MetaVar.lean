import Lott.Elab.Basic

namespace Lott

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Parser
open Lean.Parser.Term

@[macro Lott.symbolEmbed]
private
def metavarImpl : Macro := fun
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ _ #[ident@(.ident ..)],
      .atom _ "]]"
    ] => return ident
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ _ #[«fun», .atom _ "@", idx],
      .atom _ "]]"
    ] => `(([[$(.mk «fun»):Lott.Symbol]] : _ → _) $(.mk idx):term)
  | .node _ ``Lott.symbolEmbed #[
      .atom _ "[[",
      .node _ _ #[.ident .., .atom _ "$", num@(.node _ `num _)],
      .atom _ "]]"
    ] => `(.bound $(.mk num))
  | _ => Macro.throwUnsupported

elab_rules : command | `($[locally_nameless%$ln]? metavar $[(tex pre := $pre?, post := $post?)]? $names,*) => do
  let names := names.getElems.toList
  let canon :: aliases := names | throwUnsupportedSyntax
  let ns ← getCurrNamespace
  let qualified := ns ++ canon.getId
  let locallyNameless := ln.isSome

  -- Declare type and aliases.
  -- TODO: Is there any way we can make the ids have an opaque type which reveals nothing other than
  -- that they have a decidable equality relation?
  if ← getTerm then
    if locallyNameless then
      let idIdent := mkIdentFrom canon <| canon.getId.appendAfter "Id"
      elabCommand <| ← `(def $idIdent := Nat)
      elabCommand <| ← `(instance (x y : $idIdent) : Decidable (x = y) := Nat.decEq x y)
      elabCommand <| ←
        `(inductive $canon where
            | $(mkIdent `free):ident (id : $idIdent)
            | $(mkIdent `bound):ident (idx : Nat))
      elabCommand <| ← `(instance : SizeOf $canon := instSizeOfDefault $canon)
      elabCommand <| ←
        `(instance (x y : $canon) : Decidable (x = y) := match x, y with
            | .free idx, .free idy => if h : idx = idy then
                isTrue <| $(mkIdent <| canon.getId ++ `free.injEq) idx idy |>.mpr h
              else
                isFalse (h <| $(mkIdent <| canon.getId ++ `free.inj) ·)
            | .bound idxx, .bound idxy => if h : idxx = idxy then
                isTrue <| $(mkIdent <| canon.getId ++ `bound.injEq) idxx idxy |>.mpr h
              else
                isFalse (h <| $(mkIdent <| canon.getId ++ `bound.inj) ·)
            | .free _, .bound _
            | .bound _, .free _ => isFalse nofun)
      elabCommand <| ← `(instance : Coe $idIdent $canon where coe := .free)
    else
      elabCommand <| ← `(def $canon := Nat)
      elabCommand <| ← `(instance (x y : $canon) : Decidable (x = y) := Nat.decEq x y)
  else
    elabCommand <| ← `(opaque $canon : Type)

  -- Update environment extensions.
  for name in names do
    setEnv <| aliasExt.addEntry (← getEnv)
      { canon := qualified, alias := ns ++ name.getId, tex? := none }
  setEnv <| metaVarExt.addEntry (← getEnv) (qualified, locallyNameless)
  let texPrePost? ← match pre?, post? with
    | some pre, some post => pure <| some (pre.getString, post.getString)
    | none, none => pure none
    | _, _ => unreachable!
  setEnv <| symbolExt.addEntry (← getEnv)
    { qualified, normalProds := .empty, substitutions := #[], texPrePost? }

  -- Declare syntax category. For metavariables we just declare the alias name parsers directly in
  -- the syntax category. This differs from variable parsers for non-terminals, for which we declare
  -- a separate variable category, then add a category parser for the variable category to the main
  -- non-terminal symbol category.
  let catName := symbolPrefix ++ qualified
  let parserAttrName := catName.appendAfter "_parser"
  setEnv <| ← registerParserCategory (← getEnv) parserAttrName catName .symbol

  -- Declare parsers in category.
  for alias in aliases do
    let aliasName@(.str .anonymous nameStr) := alias.getId | throwUnsupportedSyntax
    let parserIdent := mkIdentFrom alias <| canon.getId ++ aliasName.appendAfter "_parser"
    elabCommand <| ←
      `(@[Lott.Symbol_parser, $(mkIdent parserAttrName):ident]
        private
        def $parserIdent : Parser :=
          leadingNode $(quote catName) Parser.maxPrec <| Lott.identPrefix $(quote nameStr))

    if locallyNameless then
      let parserIdent := mkIdentFrom alias <| canon.getId ++ aliasName.appendAfter "_bound_parser"
      elabCommand <| ←
        `(@[Lott.Symbol_parser, $(mkIdent parserAttrName):ident]
          private
          def $parserIdent : Parser :=
            leadingNode $(quote catName) Parser.maxPrec <|
              Lott.identPrefix $(quote nameStr) >> "$" >> num)

  let parserIdent := mkIdentFrom canon <| canon.getId.appendAfter "_idx_parser"
  elabCommand <| ←
    `(@[Lott.Symbol_parser, $(mkIdent parserAttrName):ident]
      private
      def $parserIdent : TrailingParser :=
        trailingNode $(quote catName) Parser.maxPrec 0 <|
          checkNoWsBefore >> "@" >> checkLineEq >> (Parser.ident <|> Parser.numLit))

end Lott
