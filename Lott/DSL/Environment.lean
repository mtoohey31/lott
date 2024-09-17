import Lean.Data.Trie
import Lean.Environment
import Lott.DSL.IR

namespace Lott.DSL

open Lean
open Lean.Data

structure SymbolAlias where
  canon : Name
  alias : Name

instance : Inhabited SymbolAlias where default := { canon := default, alias := default }

structure SymbolState where
  byAlias : Trie SymbolAlias
  allCanon : NameSet

instance : Inhabited SymbolState where default := { byAlias := default, allCanon := default }

initialize symbolExt : PersistentEnvExtension SymbolAlias SymbolAlias SymbolState ←
  registerPersistentEnvExtension {
  mkInitial := return default
  addImportedFn := fun symss => return {
    byAlias :=
      symss.flatten.foldl (init := .empty) fun acc a => acc.upsert a.alias.toString fun _ => a
    allCanon := symss.flatten.map (·.canon) |> RBTree.fromArray (cmp := Name.quickCmp)
  }
  addEntryFn := fun { byAlias, allCanon } a => {
    byAlias := byAlias.insert a.alias.toString a
    allCanon := allCanon.insert a.canon
  }
  exportEntriesFn := fun { byAlias, .. } => byAlias.values
}

structure Judgement where
  name : Name
  ir : Array IR

structure JudgementState where
  byName : NameMap Judgement
  all : NameSet

instance : Inhabited JudgementState where default := { byName := default, all := default }

initialize judgementExt : PersistentEnvExtension Judgement Judgement JudgementState ← registerPersistentEnvExtension {
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
