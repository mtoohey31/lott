import Lott.Elab.Basic
import Lott.Parser.JudgementComprehension

namespace Lott

open Lean
open Lean.Elab

@[macro judgementEmbed]
private
def judgementComprehensionImpl : Macro := fun stx => do
  let `([[</ $«judgement»:Lott.Judgement // $[(tex := $_)]? $p:term in $c:term $[notex%$nt]? />]]) := stx
    | Macro.throwUnsupported
  `(∀ x ∈ $c, let $p:term := x; [[$«judgement»:Lott.Judgement]])

@[lott_tex_elab judgementComprehension]
private
def judgementComprehensionTexElab : TexElab := fun profile ref stx => do
  let `(judgementComprehension| </ $«judgement»:Lott.Judgement // $[(tex := $tex?)]? $pat:term in $collection:term $[notex%$nt]? />) := stx
    | throwUnsupportedSyntax
  let judgementTex ← texElabSymbolOrJudgement «judgement».raw.getKind profile ref «judgement»
  if nt.isSome then
    if let some tex := tex? then
      logWarningAt tex "notex takes precedence over tex"
    return s!"\\lottjudgementcomprehension\{{judgementTex}}"

  if let some tex := tex? then
    return s!"\\lottjudgementcomprehensioncustom\{{judgementTex}}\{{tex}}"

  let some patSubstring := pat.raw.getSubstring? (withLeading := false) (withTrailing := false)
    | throwUnsupportedSyntax
  let patTex := patSubstring.toString.texEscape
  let some collectionSubstring :=
    collection.raw.getSubstring? (withLeading := false) (withTrailing := false)
    | throwUnsupportedSyntax
  let collectionTex := collectionSubstring.toString.texEscape
  return s!"\\lottjudgementcomprehensionpatcollection\{{judgementTex}}\{{patTex}}\{{collectionTex}}"

end Lott
