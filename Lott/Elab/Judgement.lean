import Lott.Elab.Basic
import Lott.Parser

namespace Lott

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Meta
open Lean.Parser
open Lean.Parser.Command
open Lean.Parser.Term

private
def judgementPrefix := `Lott.Judgement

elab_rules : command | `(judgement_syntax $[$ps]* : $name $[(id $ids?,*)]? $[(tex $[$texProfile?s]? := $tex?s)]*) => do
  -- Declare syntax category.
  let ns ← getCurrNamespace
  let qualified := ns ++ name.getId
  let catName := judgementPrefix ++ qualified
  let parserAttrName := catName.appendAfter "_parser"
  setEnv <| ← Parser.registerParserCategory (← getEnv) parserAttrName catName .symbol

  -- Add to environment extension.
  let ir ← ps.mapM IR.ofStx
  let ids := ids?.getD (.mk #[]) |>.getElems |>.map TSyntax.getId
  let profiles := Std.HashSet.toArray <| Std.HashSet.ofArray <|
    texProfile?s.filterMap <| Option.map TSyntax.getId
  setEnv <| judgementExt.addEntry (← getEnv) { name := qualified, ir, ids, profiles }

  -- Declare parser.
  let (val, type) ← IR.toParser ir name.getId judgementPrefix
  if type != (← `(term| Parser)) then throwError "invalid left recursive judgement syntax"
  let parserIdent := mkIdentFrom name <| name.getId.appendAfter "_parser"
  elabCommand <| ←
    `(@[Lott.Judgement_parser, $(mkIdent parserAttrName):ident]
      private
      def $parserIdent : Parser := $val)

  -- Define macro and tex elab.
  let patternArgs ← IR.toPatternArgs ir

  if ← getTerm then
    let macroSeqItems ← IR.toMacroSeqItems ir name.getId ids #[]
    let exprArgs ← IR.toExprArgs ir ids #[]

    let macroName := mkIdentFrom name <| name.getId.appendAfter "Impl"
    elabCommand <| ←
      `(@[macro $(mkIdent `Lott.judgementEmbed)]
        private
        def $macroName : Macro := fun stx => do
          let Lean.Syntax.node _ ``Lott.judgementEmbed #[
            Lean.Syntax.atom _ "[[",
            Lean.Syntax.node _ $(quote catName) #[$patternArgs,*],
            Lean.Syntax.atom _ "]]"
          ] := stx | Macro.throwUnsupported
          $macroSeqItems*
          return Syntax.mkApp (mkIdent $(quote qualified)) #[$exprArgs,*])

  if ← getTexOutputSome then
    let catIdent := mkIdent catName
    let texSeqItems ← IR.toTexSeqItems ir name.getId
    let (alts, defaults) := texProfile?s.zip tex?s |>.partition fun (profile?, _) => profile?.isSome

    let profileAlternatives ← alts.mapM fun (profile?, tex) => do
      `(doSeqItem| if profile == $(quote profile?.get!.getId) then return $tex)

    let rest ← match defaults with
      | ⟨[]⟩ => do
        let joinArgs := IR.toJoinArgs ir
        `(term| " ".intercalate [$joinArgs,*])
      | ⟨[(_, tex)]⟩ => pure tex
      | _ => throwUnsupportedSyntax

    let texElabName := mkIdentFrom name <| name.getId.appendAfter "TexElab"
    elabCommand <| ←
      `(@[lott_tex_elab $catIdent]
        private
        def $texElabName : TexElab := fun profile ref stx => do
          let Lean.Syntax.node _ $(quote catName) #[$patternArgs,*] := stx
            | throwUnsupportedSyntax
          $texSeqItems*
          $profileAlternatives*
          return $rest)

private
inductive RulesOrTerm
  | rules (r : TSyntaxArray `Lott.InferenceRule)
  | term (t : Term)

private
def elabJudgementDecls (jds : Array Syntax) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let jds ← jds.mapM fun jd => do
    let `(JudgementDecl| judgement $name $rhs) := jd | throwUnsupportedSyntax
    let (name, rulesOrTerm) ← match rhs with
      | `(JudgementDeclRHS| where $r:Lott.InferenceRule*) => pure (name, RulesOrTerm.rules r)
      | `(JudgementDeclRHS| := $t:term) => pure (name, .term t)
      | _ => throwUnsupportedSyntax
    let some jd := judgementExt.getState (← getEnv) |>.byName.find? <| ns ++ name.getId
      | throwError "judgement_syntax for {name} not given before use in judgement"
    return (name, jd, rulesOrTerm)

  if ← getTerm then
    elabMutualCommands <| ← jds.mapM fun (name, { ir, ids, .. }, rulesOrTerm) => do
      match rulesOrTerm with
      | .rules r =>
        let qualified := ns ++ name.getId
        let type ← IR.toTypeArrSeq ir (← `(term| Prop)) ids #[]
        let catName := judgementPrefix ++ qualified
        let ctors ← r.mapM fun rule => do
          let `(InferenceRule| $upper:Lott.InferenceRuleUpper* $[─]* $name $[(comment $[$_]? $[:= $_]?)]* $binders* $[notex%$nt?]? $conclusion:Lott.Judgement) := rule
            | throwUnsupportedSyntax
          let conclusionKind := conclusion.raw.getKind
          if conclusionKind != catName then
            throwErrorAt conclusion
              "found conclusion judgement syntax kind{indentD conclusionKind}\
              expected to find kind{indentD catName}\
              all conclusions of inference rules in a judgement declaration must be the judgement which is being defined"

          let ctorType ← upper.foldrM (init := ← `(term| [[$conclusion:Lott.Judgement]]))
            fun
              | `(InferenceRuleUpper| notex $«judgement»:Lott.Judgement), acc =>
                `([[$«judgement»:Lott.Judgement]] → $acc)
              | `(InferenceRuleUpper| notex $i:ident := $sym), acc =>
                `(let $i := [[$sym:Lott.Symbol]]; $acc)
              | `(InferenceRuleUpper| notex for $_ $«judgement»:Lott.Judgement), acc =>
                `([[$«judgement»:Lott.Judgement]] → $acc)
              | `(InferenceRuleUpper| notex for $_:ident $i:ident := $sym), acc =>
                `(let $i := [[$sym:Lott.Symbol]]; $acc)
              | `(InferenceRuleUpper| $«judgement»:Lott.Judgement), acc =>
                `([[$«judgement»:Lott.Judgement]] → $acc)
              | `(InferenceRuleUpper| $i:ident := $sym), acc =>
                `(let $i := [[$sym:Lott.Symbol]]; $acc)
              | _, _ => throwUnsupportedSyntax
          `(ctor| | $name:ident $binders* : zeta_reduce% $ctorType)

        `(inductive $name : $type where $ctors*)
      | .term t => `(def $name := $t)
  else
    for (name, _) in jds do
      elabCommand <| ← `(opaque $name : Type)

  if ← getTexOutputSome then
    for (name, { ir, profiles, .. }, rulesOrTerm) in jds do
      let .rules r := rulesOrTerm | continue

      for profile in profiles.push default do
        let qualified := ns ++ name.getId
        let catName := judgementPrefix ++ qualified
        writeTexOutput (qualified ++ profile) do
          let nameTex := name.getId.getFinal.getString!.pascalToTitle.texEscape
          let exampleStx := mkNode catName <| ← toExampleSyntax ir qualified profile
          let syntaxTex ← liftTermElabM <| texElabSymbolOrJudgement catName profile name exampleStx
          let inferenceRuleTexs ← r.filterMapM fun rule => do
            let `(InferenceRule| $upper:Lott.InferenceRuleUpper* $[─]* $name $[(comment $[$commentProfile?s]? $[:= $comment?s]?)]* $_* $[notex%$nt?]? $conclusion:Lott.Judgement) := rule
              | throwUnsupportedSyntax

            if nt?.isSome then
              return none

            let nameTex := name.getId.getFinal.getString!.texEscape
            let hypothesesTexs ← upper.filterMapM fun
              | `(InferenceRuleUpper| notex $_:Lott.InferenceRuleUpper) => return none
              | `(InferenceRuleUpper| notex for $profile' $upper:Lott.InferenceRuleUpper) => do
                if profile == profile'.getId then
                  return none
                match upper with
                | `(InferenceRuleUpper| $i:ident := $sym) => do
                  let catName := sym.raw.getKind
                  let env ← getEnv
                  let mut idTex := i.getId.toString false |>.texEscape
                  if let some qualified := catName.erasePrefix? symbolPrefix then
                    if let some { texPrePost? := some (texPre, texPost), .. } :=
                      symbolExt.getState env |>.find? qualified then
                      idTex := s!"{texPre} {idTex} {texPost}"
                  let symTex ← liftTermElabM <| texElabSymbolOrJudgement catName profile sym sym
                  return s!"\n\\lottlet\{{idTex}}\{{symTex}}"
                | `(InferenceRuleUpper| $hyp:Lott.Judgement) => do
                  let hypTex ← liftTermElabM <|
                    texElabSymbolOrJudgement hyp.raw.getKind profile hyp hyp
                  return s!"\n\\lotthypothesis\{{hypTex}}"
                | _ => throwUnsupportedSyntax
              | `(InferenceRuleUpper| $i:ident := $sym) => do
                let catName := sym.raw.getKind
                let env ← getEnv
                let mut idTex := i.getId.toString false |>.texEscape
                if let some qualified := catName.erasePrefix? symbolPrefix then
                  if let some { texPrePost? := some (texPre, texPost), .. } :=
                    symbolExt.getState env |>.find? qualified then
                    idTex := s!"{texPre} {idTex} {texPost}"
                let symTex ← liftTermElabM <| texElabSymbolOrJudgement catName profile sym sym
                return s!"\n\\lottlet\{{idTex}}\{{symTex}}"
              | `(InferenceRuleUpper| $hyp:Lott.Judgement) => do
                let hypTex ← liftTermElabM <|
                  texElabSymbolOrJudgement hyp.raw.getKind profile hyp hyp
                return s!"\n\\lotthypothesis\{{hypTex}}"
              | _ => throwUnsupportedSyntax
            let mut hypothesesTex := "\\\\".intercalate hypothesesTexs.toList
            if hypothesesTex == "" then
              hypothesesTex := "\n\\\\\\\\"
            let conclusionTex ← liftTermElabM <|
              texElabSymbolOrJudgement catName profile conclusion conclusion
            let (alts, defaults) := commentProfile?s.zip comment?s |>.partition fun (profile?, _) =>
              profile?.isSome

            let default? ← match defaults with
              | ⟨[]⟩ => pure none
              | ⟨[(_, default)]⟩ => pure default
              | ⟨_⟩ => throwUnsupportedSyntax

            let comment? := Option.getD (dflt := default?) <| Option.map Prod.snd <|
              alts.find? fun (p?, _) => p?.map TSyntax.getId == some profile

            if let some comment := comment? then
              return s!"\\lottinferencerulecommented\{{nameTex}}\{{comment.getString}}\{{hypothesesTex}\n}\{{conclusionTex}}\n"
            return s!"\\lottinferencerule\{{nameTex}}\{{hypothesesTex}\n}\{{conclusionTex}}\n"

          let inferenceRulesTex := "\\lottinferencerulesep\n".intercalate inferenceRuleTexs.toList
          return s!"\\lottjudgement\{{nameTex}}\{{syntaxTex}}\{\n{inferenceRulesTex}}\n"

elab_rules : command
  | `($jd:Lott.JudgementDecl) => elabJudgementDecls #[jd]
  | `(mutual $[$jds:Lott.JudgementDecl]* end) => elabJudgementDecls jds

@[term_elab zetaReduce]
partial
def elabZetaReduce : TermElab := fun stx expectedType? => do
  let `(zeta_reduce% $t) := stx | throwUnsupportedSyntax
  let e ← elabTerm t expectedType?
  liftMetaM <| Meta.zetaReduce e

end Lott
