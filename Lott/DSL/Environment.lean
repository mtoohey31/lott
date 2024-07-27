import Lean.Data.NameMap
import Lean.Environment

namespace Lott.DSL

open Lean

structure LottSymbolAlias where
  canon : Name
  alias : Name

instance : Inhabited LottSymbolAlias where default := { canon := default, alias := default }

structure LottSymbolAliasState where
  byAlias : NameMap LottSymbolAlias

instance : Inhabited LottSymbolAliasState where default := { byAlias := default }

initialize lottSymbolAliasExt : PersistentEnvExtension LottSymbolAlias LottSymbolAlias LottSymbolAliasState ← registerPersistentEnvExtension {
  mkInitial := return { byAlias := mkNameMap LottSymbolAlias },
  addImportedFn := fun symss => return {
    byAlias :=
      symss.flatten.foldl (init := mkNameMap LottSymbolAlias) fun acc a => acc.insert a.alias a
  },
  addEntryFn := fun s a => { s with byAlias := s.byAlias.insert a.alias a },
  exportEntriesFn :=
    fun s => s.byAlias.fold (cmp := Name.quickCmp) (init := #[]) fun acc _ a => acc.push a,
}

structure LottJudgementSyntax where
  name : Name
  ps : TSyntaxArray [`Lean.Parser.Syntax.atom, `ident]

instance : Inhabited LottJudgementSyntax where default := { name := default, ps := default }

structure LottJudgementSyntaxState where
  byName : NameMap LottJudgementSyntax

instance : Inhabited LottJudgementSyntaxState where default := { byName := default }

initialize lottJudgementSyntaxExt : PersistentEnvExtension LottJudgementSyntax LottJudgementSyntax LottJudgementSyntaxState ← registerPersistentEnvExtension {
  mkInitial := return { byName := mkNameMap LottJudgementSyntax },
  addImportedFn := fun symss => return {
    byName :=
      symss.flatten.foldl (init := mkNameMap LottJudgementSyntax) fun acc a => acc.insert a.name a
  },
  addEntryFn := fun s a => { s with byName := s.byName.insert a.name a },
  exportEntriesFn :=
    fun s => s.byName.fold (cmp := Name.quickCmp) (init := #[]) fun acc _ a => acc.push a,
}

end Lott.DSL
