import Lott.Elab.Basic
import Lott.Parser.UniversalJudgement

namespace Lott

open Lean
open Lean.Elab

@[macro judgementEmbed]
private
def universalJudgementImpl : Macro
  | `([[∀ $[$binders]* $[$type?]?, $«judgement»:Lott.Judgement]]) =>
    ``(∀ $binders* $[$type?:typeSpec]?, [[$«judgement»:Lott.Judgement]])
  | `([[∀ $i:ident $bp:binderPred, $«judgement»:Lott.Judgement]]) =>
    ``(∀ $i:ident, satisfies_binder_pred% $i $bp → [[$«judgement»:Lott.Judgement]])
  | `([[∀ $i:ident, $«judgement»:Lott.Judgement]]) =>
    ``(∀ $i:ident, [[$«judgement»:Lott.Judgement]])
  | _ => Macro.throwUnsupported

@[lott_tex_elab universalJudgement]
private
def universalJudgementTexElab : TexElab := fun profile ref stx => do
  let `(universalJudgement| ∀ $binders* $[$type?]?, $«judgement»:Lott.Judgement) := stx
    | throwUnsupportedSyntax
  let binderTexs := ", ".intercalate <| Array.toList <| binders.map fun
    | `(hole| _) => "_"
    | `(bracketedBinder| {$is*}) => ", ".intercalate <| Array.toList <| is.map fun
      | `(hole| _) => "_"
      | `(ident| $i) => i.getId.toString false |>.texEscape
    | `(ident| $i) => i.getId.toString false |>.texEscape
  -- NOTE: type is intentionally omitted.
  let judgementTex ← texElabSymbolOrJudgement judgement.raw.getKind profile ref «judgement»

  let opts ← getOptions
  let locallyNameless := opts.get lott.tex.locallyNameless.name lott.tex.locallyNameless.defValue
  if !locallyNameless then
    return judgementTex

  return s!"\\lottsym\{∀} \\, {binderTexs}, {judgementTex}"

@[lott_tex_elab universalPredJudgement]
private
def universalPredJudgementTexElab : TexElab
  | profile, ref, `(universalPredJudgement| ∀ $i:ident $bp:binderPred, $«judgement»:Lott.Judgement) => do
    let identTex := i.getId.toString false |>.texEscape
    let bpSym := bp.raw.getArg 0 |>.getAtomVal
    let some bpTermSubstring :=
      bp.raw.getArg 1 |>.getSubstring? (withLeading := false) (withTrailing := false)
      | throwUnsupportedSyntax
    let bpTermTex := bpTermSubstring.toString.texEscape
    let judgementTex ← texElabSymbolOrJudgement judgement.raw.getKind profile ref «judgement»

    let opts ← getOptions
    let locallyNameless := opts.get lott.tex.locallyNameless.name lott.tex.locallyNameless.defValue
    if bpSym == "∉" && !locallyNameless then
      return judgementTex

    return s!"\\lottsym\{∀} \\, {identTex} \\, \\lottsym\{{bpSym}} \\, {bpTermTex}, {judgementTex}"
  | _, _, _ => throwUnsupportedSyntax

end Lott
