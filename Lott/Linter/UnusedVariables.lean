import Lean.Linter

namespace Lean.Linter

/- Term embedding syntax. -/

/-
You can't put a hole inside an embedding to ignore something, so it's generally desirable to not be
bugged about embedding pattern variables being unused.
-/
register_option linter.unusedVariables.lottSymbolEmbeddingPatternVars : Bool := {
  defValue := false
  descr :=
    "enable the 'unused variables' linter to mark unused lott symbol embedding pattern variables"
}

def getLinterUnusedVariablesLottSymbolEmbeddingPatternVars (o : Options) : Bool :=
  o.get linter.unusedVariables.lottSymbolEmbeddingPatternVars.name
    (Lean.Linter.getLinterUnusedVariables o &&
      linter.unusedVariables.lottSymbolEmbeddingPatternVars.defValue)

@[unused_variables_ignore_fn]
private
def symbolEmbeddingPatternVars : Lean.Linter.IgnoreFunction := fun _ stack opts =>
  !getLinterUnusedVariablesLottSymbolEmbeddingPatternVars opts && (
    let stackBeforeMatchAlt := stack.takeWhile fun (stx, _) =>
      !stx.isOfKind ``Lean.Parser.Term.matchAlt
    stackBeforeMatchAlt.length != stack.length &&
      stackBeforeMatchAlt.any fun (stx, _) => stx.isOfKind `Lott.symbolEmbed
  )

end Lean.Linter
