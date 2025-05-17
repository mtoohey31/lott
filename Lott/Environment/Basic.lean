import Lean.Data.Trie
import Lean.Environment
import Lott.IR

namespace Lott

open Lean
open Lean.Data

structure Alias where
  canon : Name
  alias : Name
  tex? : Option String

instance : Inhabited Alias where default := { canon := default, alias := default, tex? := default }

structure AliasState where
  byAlias : Trie Alias
  allCanon : NameSet

instance : Inhabited AliasState where default := { byAlias := default, allCanon := default }

initialize aliasExt : PersistentEnvExtension Alias Alias AliasState ←
  registerPersistentEnvExtension {
  mkInitial := return default
  addImportedFn := fun aliasss => return {
    byAlias :=
      aliasss.flatten.foldl (init := .empty) fun acc a => acc.upsert a.alias.toString fun _ => a
    allCanon := aliasss.flatten.map (·.canon) |> RBTree.fromArray (cmp := Name.quickCmp)
  }
  addEntryFn := fun { byAlias, allCanon } a => {
    byAlias := byAlias.insert a.alias.toString a
    allCanon := allCanon.insert a.canon
  }
  exportEntriesFn := fun { byAlias, .. } => byAlias.values
}

structure Symbol where
  qualified : Name
  normalProds : NameMap (Array IR)
  substitutions : Array (Name × Name)
  texPrePost? : Option (String × String)

instance : Inhabited Symbol where
  default := {
    qualified := default
    normalProds := default
    substitutions := default
    texPrePost? := default
  }

abbrev SymbolState := NameMap Symbol

initialize symbolExt : PersistentEnvExtension Symbol Symbol SymbolState ←
  registerPersistentEnvExtension {
  mkInitial := return default
  addImportedFn := fun symss =>
    return symss.flatten.foldl (init := mkNameMap _) fun acc sym => acc.insert sym.qualified sym
  addEntryFn := fun st sym => st.insert sym.qualified sym
  exportEntriesFn := RBMap.fold (cmp := Name.quickCmp) (init := #[]) fun acc _ sym => acc.push sym
}

structure Judgement where
  name : Name
  ir : Array IR
  ids : Array Name
  profiles : Array Name

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

structure Child where
  canon : Name
  parent : Name

abbrev ChildState := NameMap Child

initialize childExt : PersistentEnvExtension Child Child ChildState ← registerPersistentEnvExtension {
  mkInitial := return default
  addImportedFn := fun children =>
    return children.flatten.foldl (init := mkNameMap _) fun acc child => acc.insert child.canon child
  addEntryFn := fun st child => st.insert child.canon child
  exportEntriesFn := RBMap.fold (cmp := Name.quickCmp) (init := #[]) fun acc _ child => acc.push child
}

end Lott
