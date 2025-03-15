import Lean

namespace Lott

open Lean
open Lean.Elab.Command

register_option lott.term : Bool := {
  defValue := true
  descr := "create inductives, substitutions, free vars functions, locally closed inductives, and more"
}

register_option lott.tex.example.comprehensionNoTex : Bool := {
  defValue := true
  descr := "use notex option for example syntax comprehensions in tex output"
}

register_option lott.tex.example.singleProductionInline : Bool := {
  defValue := true
  descr := "inline example syntax of nonterminals with a single production in tex output"
}

register_option lott.tex.locallyNameless : Bool := {
  defValue := true
  descr := "show locally nameless operations in tex output"
}

register_option lott.tex.output.dir : String := {
  defValue := "."
  descr := "directory where tex output files should be saved"
}

register_option lott.tex.output.sourceRelative : Bool := {
  defValue := true
  descr := "when output.dir is relative, whether it should be considered relative to the source file's parent, or to the Lean process's working directory"
}

register_option lott.tex.output.makeDeps : Bool := {
  defValue := false
  descr := "also output .d files for make alongside tex"
}

def getTexOutputSome : CommandElabM Bool := return (← getOptions).contains lott.tex.output.dir.name

def getTerm : CommandElabM Bool := return (← getOptions).get lott.term.name lott.term.defValue

end Lott
