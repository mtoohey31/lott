import Lott.Elab.Basic
import Lott.Parser.NotExistentialJudgement

namespace Lott

open Lean
open Lean.Elab

@[macro judgementEmbed]
private
def existentialJudgementImpl : Macro
  | `([[∄ $binders, $«judgement»:Lott.Judgement]]) =>
    ``(¬(∃ $binders, [[$«judgement»:Lott.Judgement]]))
  | _ => Macro.throwUnsupported

@[lott_tex_elab notExistentialJudgement]
private
def notExistentialJudgementTexElab : TexElab := fun ref stx => do
  let `(notExistentialJudgement| ∄ $binders, $«judgement»:Lott.Judgement) := stx
    | throwUnsupportedSyntax
  let binderIdents ← match binders with
    | `(explicitBinders| $bis:binderIdent* $[: $_]?) => pure bis
    | `(explicitBinders| $[($bis* : $_)]*) => pure bis.flatten
    | _ => throwUnsupportedSyntax
  let binderTexs := ", ".intercalate <| Array.toList <| ← binderIdents.mapM fun
    | `(binderIdent| _) => return "_"
    | `(binderIdent| $i:ident) => return i.getId.toString false |>.texEscape
    | _ => throwUnsupportedSyntax
  -- NOTE: type is intentionally omitted.
  let judgementTex ← texElabSymbolOrJudgement judgement.raw.getKind ref «judgement»

  return s!"\\lottsym\{∄} \\, {binderTexs}, {judgementTex}"

end Lott
