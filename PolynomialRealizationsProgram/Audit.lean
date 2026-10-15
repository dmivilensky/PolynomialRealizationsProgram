import Lean

/-!
Articles: 2606.16671v2 and 2610.05164v2 — full-package trust checks.
Use: `audit` runs in each article's `Check` after its `Article` showcase is imported.
It selects declarations by their defining module, checks every source is imported,
and compares stored axiom reports with a direct traversal of types and proof bodies.
Source: Lean.Environment and Lean.Util.CollectAxioms — module ownership and axiom collection.
This is elaboration tooling; it contributes no mathematical assumption.
-/

namespace PolynomialRealizationsProgram
open Lean Elab Command

/-- Audit every declaration defined by modules under the supplied article root.

`root` is the escaped Lean module stem; `directory` is its source directory.
Ownership is determined by defining module, so private/generated names outside
the public namespace are included. Every source file must occur in the import closure.

The audit first rejects unsafe article declarations except the single untrusted
energy-witness proposal helper. It collects transitive axioms with `collectAxioms`,
then independently traverses types, opaque proof bodies and inductive constructors.
The two axiom sets must agree and contain only the declared logical allowlist.
Imported-but-unused runtime axioms are reported separately.

Use: both articles' `Check` entry points call this routine after their complete
`Article` imports. It checks the trust boundary for all theorem chains in
2606.16671v2 and 2610.05164v2; it supplies no mathematical premise.
Source: Lean.Environment module ownership and Lean.Util.CollectAxioms. -/
def audit (root : Name) (directory : String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let allowed : NameSet := [``propext, ``Classical.choice, ``Quot.sound].foldl (·.insert ·) {}
  let owner (name : Name) : Name := match env.getModuleIdxFor? name with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule
  let owned (name : Name) := root.isPrefixOf (owner name)
  -- Module ownership is crucial: private names and generated tactic helpers can
  -- have names that do not begin with the public article namespace.
  let mut count : Nat := 0
  let mut unsafeHelpers : Array Name := #[]
  let mut reported : NameSet := {}
  let mut todo : Array Name := #[]
  for (name, info) in env.constants.toList do
    if owned name then
      count := count + 1
      if info.isUnsafe then
        -- Only the untrusted witness-proposal tactic may contain unsafe runtime code.
        -- Its generated data and certificate proofs remain safe kernel declarations.
        unless owner name == `«2606.16671v2».Numerics.EnergyWitnessGenerator &&
            name.getString! == "unsafe_1" && unsafeHelpers.isEmpty do
          throwError "Unsafe article declaration: {name}"
        unsafeHelpers := unsafeHelpers.push name
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "{name} depends on forbidden axiom {ax}"
        reported := reported.insert ax
      todo := todo.push name
  let mut seen : NameSet := {}
  let mut direct : NameSet := {}
  -- Traverse the actual imported expressions independently of collectAxioms.
  -- Opaque theorem bodies matter here: inspecting types alone misses proof dependencies.
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      let some info := env.find? name | throwError "Missing declaration body: {name}"
      if info matches .axiomInfo _ then direct := direct.insert name
      todo := todo ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        todo := todo ++ value.getUsedConstants
      if info matches .inductInfo _ then
        -- Constructor types can mention propositions not exposed in the inductive's own type.
        if let .inductInfo value := info then todo := todo ++ value.ctors.toArray
  unless direct.toArray.qsort Name.lt == reported.toArray.qsort Name.lt do
    throwError "Axiom report differs from direct traversal: {reported.toArray} versus {direct.toArray}"
  let files ← liftIO <| (System.FilePath.mk directory).walkDir
  -- This guards against a successful audit of an accidentally incomplete import list.
  let mut sources : Nat := 0
  for file in files do
    if file.extension == some "lean" then
      let relative := file.toString.drop (directory.length + 1) |>.toString
      let parts := (relative.dropEnd 5).toString.splitOn "/"
      let module := parts.foldl Name.str root
      unless module == env.mainModule || env.header.moduleNames.contains module do
        throwError "Source is absent from full check: {file}"
      sources := sources + 1
  let mut imported : Array Name := #[]
  -- Presence in the imported environment is weaker than use in a proof. Report
  -- the full list as well as the already verified transitive dependency set.
  for (name, info) in env.constants.toList do
    if info matches .axiomInfo _ then imported := imported.push name
  logInfo m!"{root}: {sources} source files; {count} owned declarations; used axioms {direct.toArray.qsort Name.lt}"
  logInfo m!"Unsafe witness-proposal helpers (outside mathematical proofs): {unsafeHelpers}"
  logInfo m!"All axiom declarations present in the imported environment: {imported.qsort Name.lt}"

end PolynomialRealizationsProgram
