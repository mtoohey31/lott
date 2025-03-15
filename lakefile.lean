import Lake
open Lake DSL

-- TODO: Use lib leanOptions for everything instead of args once string escaping is fixed.

package lott where
  moreGlobalServerArgs := #[s!"-Dweak.lott.tex.output.dir={__dir__}"]

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.17.0"

lean_lib Lott

lean_lib LottExamples where
  leanOptions := #[⟨`lott.tex.output.sourceRelative, false⟩]
  moreLeanArgs := #[s!"-Dlott.tex.output.dir={__dir__}"]
