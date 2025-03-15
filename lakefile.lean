import Lake

open Lake DSL

def noterm := get_config? noterm |>.isSome

def notex := get_config? notex |>.isSome

-- TODO: Use lib leanOptions for everything instead of args once string escaping is fixed.
def args := if notex then #[] else #[s!"-Dweak.lott.tex.output.dir={__dir__}"]

package lott where
  moreGlobalServerArgs := args

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.17.0"

lean_lib Lott

lean_lib LottExamples where
  leanOptions := (if noterm then #[⟨`lott.term, false⟩] else #[]) ++
    if notex then #[] else #[⟨`lott.tex.output.sourceRelative, false⟩]
  moreLeanArgs := args
