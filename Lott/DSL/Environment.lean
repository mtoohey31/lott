import Lean.Data.NameMap
import Lean.Environment

namespace Lott.DSL

open Lean

structure LottSymbolAlias where
  canon : Name
  alias : Name

instance : Inhabited LottSymbolAlias where default := { canon := default, alias := default }

structure LottSymbolState where
  byAlias : NameMap LottSymbolAlias
  allCanon : NameSet

instance : Inhabited LottSymbolState where default := { byAlias := default, allCanon := default }

initialize lottSymbolExt : PersistentEnvExtension LottSymbolAlias LottSymbolAlias LottSymbolState ←
  registerPersistentEnvExtension {
  mkInitial := return default
  addImportedFn := fun symss => return {
    byAlias :=
      symss.flatten.foldl (init := mkNameMap LottSymbolAlias) fun acc a => acc.insert a.alias a
    allCanon := symss.flatten.map (·.canon) |> RBTree.fromArray (cmp := Name.quickCmp)
  }
  addEntryFn := fun { byAlias, allCanon } a => {
    byAlias := byAlias.insert a.alias a
    allCanon := allCanon.insert a.canon
  }
  exportEntriesFn := fun { byAlias, .. } =>
    byAlias.fold (cmp := Name.quickCmp) (init := #[]) fun acc _ a => acc.push a
}

structure LottJudgement where
  name : Name
  ps : TSyntaxArray [`Lean.Parser.Syntax.atom, `ident]

structure LottJudgementState where
  byName : NameMap LottJudgement
  all : NameSet

instance : Inhabited LottJudgementState where default := { byName := default, all := default }

initialize lottJudgementExt : PersistentEnvExtension LottJudgement LottJudgement LottJudgementState ← registerPersistentEnvExtension {
  mkInitial := return default
  addImportedFn := fun jds => return {
    byName := jds.flatten.foldl (init := mkNameMap _) fun acc jd => acc.insert jd.name jd
    all := jds.flatten.map (·.name) |> RBTree.fromArray (cmp := Name.quickCmp)
  }
  addEntryFn := fun { byName, all } jd => {
    byName := byName.insert jd.name jd
    all := all.insert jd.name
  }
  exportEntriesFn := fun { byName, .. } =>
    byName.fold (cmp := Name.quickCmp) (init := #[]) fun acc _ jd => acc.push jd
}

end Lott.DSL
