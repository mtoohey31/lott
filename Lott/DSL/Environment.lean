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

initialize lottSymbolAliasExt : PersistentEnvExtension LottSymbolAlias LottSymbolAlias LottSymbolAliasState ←
  registerPersistentEnvExtension {
  mkInitial := return { byAlias := mkNameMap LottSymbolAlias },
  addImportedFn := fun symss => return {
    byAlias :=
      symss.flatten.foldl (init := mkNameMap LottSymbolAlias) fun acc a => acc.insert a.alias a
  },
  addEntryFn := fun s a => { s with byAlias := s.byAlias.insert a.alias a },
  exportEntriesFn :=
    fun s => s.byAlias.fold (cmp := Name.quickCmp) (init := #[]) fun acc _ a => acc.push a,
}

structure LottJudgementSyntaxState where
  byName : NameMap <| TSyntaxArray [`Lean.Parser.Syntax.atom, `ident]

instance : Inhabited LottJudgementSyntaxState where default := { byName := default }

initialize lottJudgementSyntaxExt : EnvExtension LottJudgementSyntaxState ←
  registerEnvExtension <| pure { byName := mkNameMap _ }

end Lott.DSL
