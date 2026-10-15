/-
The replay routine is adapted from Lean 4's LeanChecker.lean.
Copyright (c) 2023 Kim Morrison. All rights reserved.
Authors: Kim Morrison, Sebastian Ullrich.
Released under the Apache 2.0 license: https://www.apache.org/licenses/LICENSE-2.0
-/
import Lean.CoreM
import Lean.Replay

/-!
Articles: 2606.16671v2 and 2610.05164v2 — optional independent proof-artifact replay.
Use: `Replay.replayModule` rechecks every exported/private declaration of a supplied module;
`Replay.replayPackage` rechecks the union for 2610.05164v2 against external imports only.
Neither mathematical library imports this executable; it adds no mathematical assumption.
Source: LeanChecker.replayFromImports and Lean.Kernel.Environment.replay — stock kernel replay.
-/

open Lean

/-- Recheck a compiled module against its imported kernel environment.
Load the exported/server/private artifact parts, collect all declarations from
the final part, and pass them to Lean's stock kernel replay. The unsafe qualifier
permits artifact/environment IO; it creates no unsafe mathematical declaration.
Use: `replayModule` and the `--file` command-line mode for independent verification
of either article's existing compiled proofs. Source: LeanChecker.replayFromImports. -/
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
the mathematical targets belong to 2606.16671v2 or 2610.05164v2. -/
unsafe def Replay.replayModule (moduleName : Name) : IO Unit := do
  Replay.replayFile (← findOLean moduleName)

/-- Replay the union of package declarations against external imports only.
This uses the same stock kernel routine, while avoiding hundreds of repeated
imports. The baseline is checked to contain no package declarations.
Use: `main --package` checks 2610.05164v2's declarations together, retaining
2606.16671v2 and external libraries as imports. Source: Lean.Kernel.Environment.replay;
this is optional checking tooling, not an additional mathematical axiom. -/
unsafe def Replay.replayPackage (modules : Array String) : IO Unit := do
  let mut imports : Array Import := #[]
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for moduleName in modules do
    let mFile ← findOLean moduleName.toName
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
    for i in parts[0].1.imports do
      unless (`«2610.05164v2»).isPrefixOf i.module || imports.any (fun j => j.module == i.module) do
        imports := imports.push i
    for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
      constants := constants.insert name ci
  let (_, state) ← importModulesCore imports |>.run
  let env ← finalizeImport state imports {} 0 false false (isModule := true)
  for (name, _) in env.constants.toList do
    -- Reject a circular baseline that already contains the declarations to be replayed.
    if (`«2610.05164v2»).isPrefixOf (Lean.privateToUserName name) then
      throw <| IO.userError s!"2610.05164v2 declaration present in external replay baseline: {name}"
  IO.println s!"Replaying {constants.size} declarations from {modules.size} modules against external imports."
  (← IO.getStdout).flush
  discard <| env.toKernelEnv.replay constants
  env.freeRegions
  IO.println s!"Kernel package replay passed for {modules.size} modules."

/-- Dispatch explicit artifact replay, whole-package replay, or named-module replay.
Without arguments, enumerate all 2610.05164v2 sources; `--package` replays their
union, while `--file` accepts explicit compiled paths. Errors stop the command.
Use: the optional replay command documented in Certificates/README.md.
Source: Lean 4's stock kernel replay, applied to the two articles' proof artifacts. -/
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
  let files ← (System.FilePath.mk "2610.05164v2").walkDir
  let modules := if args.isEmpty || args == ["--package"] then
      ((files.filter (fun p => p.extension == some "lean")).map
        (fun p => "«2610.05164v2»." ++
          (((p.withExtension "").toString.drop ("2610.05164v2".length+1)).toString.replace "/" "."))).push "«2610.05164v2»" |>.qsort
    else args.toArray
  if args == ["--package"] then
    Replay.replayPackage modules
    return
  for m in modules do
    IO.println s!"replaying {m}"
    (← IO.getStdout).flush
    Replay.replayModule m.toName
  IO.println s!"Kernel replay passed for {modules.size} «2610.05164v2» modules."
