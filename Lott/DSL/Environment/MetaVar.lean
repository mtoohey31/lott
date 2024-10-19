import Lean

namespace Lott.DSL

open Lean

initialize metaVarExt : PersistentEnvExtension (Name × Bool) (Name × Bool) (NameMap Bool) ←
  registerPersistentEnvExtension {
  mkInitial := return default
  addImportedFn := fun metaVarss =>
    return metaVarss.flatten.foldl (init := mkNameMap _) (fun acc (n, ln) => acc.insert n ln)
  addEntryFn := fun st (n, ln) => st.insert n ln
  exportEntriesFn := RBMap.fold (cmp := Name.quickCmp) (init := #[]) fun acc n ln => acc.push (n, ln)
}

end Lott.DSL
