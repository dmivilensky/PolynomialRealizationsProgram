/-
The replay routine is adapted from Lean 4's LeanChecker.lean.
Copyright (c) 2023 Kim Morrison. All rights reserved.
Authors: Kim Morrison, Sebastian Ullrich.
Released under the Apache 2.0 license: https://www.apache.org/licenses/LICENSE-2.0
-/
import Lean.CoreM
import Lean.Replay

/-!
Independent proof-artifact replay for arbitrary Lean modules and source directories.
Use: `Replay.replayModule` rechecks every exported/private declaration of a supplied module;
`Replay.replayPackage` rechecks a package union against external imports only.
Mathematical libraries do not import this executable; it adds no mathematical assumption.
Source: LeanChecker.replayFromImports and Lean.Kernel.Environment.replay — stock kernel replay.
-/

open Lean

/-- Recheck a compiled module against its imported kernel environment.
Load the exported/server/private artifact parts, collect all declarations from
the final part, and pass them to Lean's stock kernel replay. The unsafe qualifier
permits artifact/environment IO; it creates no unsafe mathematical declaration.
Use: `replayModule` and the `--file` command-line mode for independent verification
of existing compiled proofs from any source package. Source: LeanChecker.replayFromImports. -/
unsafe def Replay.replayFile (mFile : System.FilePath) : IO Unit := do
  unless ← mFile.pathExists do
    throw <| IO.userError s!"missing compiled file: {mFile}"
  let mut files := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if ← sFile.pathExists then
    files := files.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if ← pFile.pathExists then files := files.push pFile
  let parts ← readModuleDataParts files
  if h : parts.size = 0 then
    throw <| IO.userError s!"empty compiled file: {mFile}"
  else
  let (mod, _) := parts[0]
  let (_, state) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport state mod.imports {} 0 false false (isModule := true)
  let mut constants := {}
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    constants := constants.insert name ci
  discard <| env.toKernelEnv.replay constants
  env.freeRegions

/-- Resolve a Lean module name to its compiled artifact and independently replay it.
Use: `main` applies this to the selected modules. Source: `findOLean` and `replayFile`;
module ownership is supplied by the caller, without a package registry. -/
unsafe def Replay.replayModule (moduleName : Name) : IO Unit := do
  Replay.replayFile (← findOLean moduleName)

/-- Replay the union of package declarations against external imports only.
This uses the same stock kernel routine, while avoiding hundreds of repeated
imports. The baseline is checked to contain no package declarations.
Use: `Tools.Verification.Replay DIRECTORY` supplies the package root and every owned
module, retaining all other packages and community libraries as external imports. Source: Lean.Kernel.Environment.replay;
this is optional checking tooling, not an additional mathematical axiom. -/
unsafe def Replay.replayUnion (modules : Array Name) (roots : Array Name) : IO Unit := do
  let owned (name : Name) := roots.any (fun root => root.isPrefixOf name)
  let mut imports : Array Import := #[]
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut batches : Array (Name × Array Name) := #[]
  let mut dependencies : Std.HashMap Name (Array Name) := {}
  for moduleName in modules do
    let mFile ← findOLean moduleName
    unless ← mFile.pathExists do
      throw <| IO.userError s!"missing compiled file: {mFile}"
    let mut files := #[mFile]
    let sFile := OLeanLevel.server.adjustFileName mFile
    if ← sFile.pathExists then
      files := files.push sFile
      let pFile := OLeanLevel.private.adjustFileName mFile
      if ← pFile.pathExists then files := files.push pFile
    let parts ← readModuleDataParts files
    if h : parts.size = 0 then
      throw <| IO.userError s!"empty compiled file: {mFile}"
    else
    batches := batches.push (moduleName, parts[parts.size-1].1.constNames)
    dependencies := dependencies.insert moduleName (parts[0].1.imports.map (·.module))
    for i in parts[0].1.imports do
      unless owned i.module || imports.any (fun j => j.module == i.module) do
        imports := imports.push i
    for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
      constants := constants.insert name ci
  let (_, state) ← importModulesCore imports |>.run
  let env ← finalizeImport state imports {} 0 false false (isModule := true)
  for (name, _) in env.constants.toList do
    -- Reject a circular baseline that already contains the declarations to be replayed.
    let owner := match env.getModuleIdxFor? name with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.mainModule
    if owned owner then
      throw <| IO.userError s!"{roots} declaration present in external replay baseline: {name}"
  IO.println s!"Replaying {constants.size} declarations from {modules.size} modules against external imports."
  (← IO.getStdout).flush
  -- Replay dependencies first, retaining only the kernel-checked environment
  -- between batches. No owned compiled environment is imported as a baseline.
  let mut ordered : Array (Name × Array Name) := #[]
  let mut done : NameSet := {}
  while !batches.isEmpty do
    let some batch := batches.find? (fun (m, _) =>
      (dependencies[m]!).all (fun d => !owned d || done.contains d))
      | throw <| IO.userError "Missing or cyclic owned replay dependency"
    ordered := ordered.push batch
    done := done.insert batch.1
    batches := batches.filter (fun b => b.1 != batch.1)
  let mut kernelEnv := env.toKernelEnv
  let mut replayed : NameSet := {}
  for idx in [:ordered.size] do
    let (m, names) := ordered[idx]!
    let mut batchConstants : Std.HashMap Name ConstantInfo := {}
    -- Shared private declarations can be re-exported by a later artifact.
    -- Close over actual ConstantInfo dependencies, rather than only imports.
    let mut todo := names.toList
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      unless seen.contains n do
        seen := seen.insert n
        if let some ci := constants[n]? then
          if !replayed.contains n then
            batchConstants := batchConstants.insert n ci
            todo := ci.getUsedConstantsAsSet.toList ++ todo
            if let .inductInfo info := ci then
              for other in info.all do
                todo := other :: todo
                if let some (.inductInfo oi) := constants[other]? then
                  todo := oi.ctors ++ todo
          else
            -- Recheck the stored constructor/recursor against the generated one.
            if ci matches .ctorInfo _ | .recInfo _ then
              batchConstants := batchConstants.insert n ci
    IO.println s!"Kernel replay [{idx+1}/{ordered.size}] starting {m} ({names.size} declarations)"
    (← IO.getStdout).flush
    kernelEnv ← kernelEnv.replay batchConstants
    for (n, ci) in batchConstants.toList do
      if !ci.isUnsafe && !ci.isPartial then replayed := replayed.insert n
    IO.println s!"Kernel replay [{idx+1}/{ordered.size}] passed {m}"
    (← IO.getStdout).flush
  for (n, ci) in constants.toList do
    unless ci.isUnsafe || ci.isPartial || replayed.contains n do
      throw <| IO.userError s!"Unvisited owned declaration: {n}"
  env.freeRegions
  IO.println s!"Kernel package replay passed for {modules.size} modules."

/-- Backward-compatible single-root entry point. -/
unsafe def Replay.replayPackage (modules : Array Name) (root : Name) : IO Unit :=
  Replay.replayUnion modules #[root]

/-- Decode module components without splitting escaped dotted directory names.
Use: the Python directory selector supplies exact name components in its manifest.
Source: Lean.Name.str; malformed empty names are rejected before loading artifacts. -/
def Replay.moduleName (parts : Array String) : Except String Name := do
  unless !parts.isEmpty && parts.all (fun part => !part.isEmpty) do
    throw "A module needs nonempty name components"
  return parts.foldl Name.str .anonymous

/-- Dispatch explicit artifact replay, manifest-based package replay, or named modules.
Use: `python3 -m Tools.Verification.Replay DIRECTORY` discovers package sources from Lake.
Certificate verifiers can still pass named modules or explicit `--file` artifacts.
Source: Lean's stock kernel replay; no package or article names are assumed. -/
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  if args.head? == some "--file" then
    unless !args.tail.isEmpty do throw <| IO.userError "--file requires compiled files"
    for path in args.tail do
      IO.println s!"replaying {path}"
      (← IO.getStdout).flush
      Replay.replayFile path
    IO.println s!"Kernel replay passed for {args.tail.length} supplied modules."
    return
  if args.head? == some "--package" then
    unless args.length == 2 do throw <| IO.userError "--package requires a module manifest JSON"
    let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile args[1]!)
    let roots : Array Name ← match manifest.getObjVal? "roots" with
      | .ok value => do
        if (manifest.getObjVal? "root").isOk then
          throw <| IO.userError "Manifest must use root or roots, not both"
        let parts ← IO.ofExcept <| fromJson? (α := Array (Array String)) value
        parts.mapM fun root => IO.ofExcept <| Replay.moduleName root
      | .error _ => do
        let parts ← IO.ofExcept <| manifest.getObjValAs? (Array String) "root"
        let root ← IO.ofExcept <| Replay.moduleName parts
        pure #[root]
    let moduleParts ← IO.ofExcept <| manifest.getObjValAs? (Array (Array String)) "modules"
    let modules ← moduleParts.mapM fun parts => IO.ofExcept <| Replay.moduleName parts
    let owned (name : Name) := roots.any (fun root => root.isPrefixOf name)
    unless !roots.isEmpty && !modules.isEmpty && modules.all owned do
      throw <| IO.userError "Package manifest must contain owned modules under its roots"
    Replay.replayUnion modules roots
    return
  unless !args.isEmpty do
    throw <| IO.userError "Supply module names, --file artifacts, or use Tools.Verification.Replay DIRECTORY"
  for moduleName in args do
    IO.println s!"replaying {moduleName}"
    (← IO.getStdout).flush
    Replay.replayModule moduleName.toName
  IO.println s!"Kernel replay passed for {args.length} modules."
