import Lean

/-!
Articles: 2606.16671v2 and 2610.05164v2 — source-documentation checking.
Use: `Scripts/CheckDocumentation.py` uses this optional parser pass to locate actual
declarations and structure fields. An optional baseline comparison ignores only comments
and checks that the parsed executable tokens are identical, avoiding certificate regeneration.
This is source-inspection tooling, outside the mathematical import graph.
Source: Lean.Parser.testParseFile and the syntax tree's source positions.
-/

open Lean
set_option maxRecDepth 65536

/-- Encode the parsed executable syntax, omitting declaration and module prose.
Use: `main` compares these arrays against an optional source baseline. Preserving
node kinds as well as ordered atoms/identifiers checks syntax-tree identity, including
layout-sensitive grouping, without trusting textual comment removal.
Source: Lean.Syntax; the two articles' mathematical assertions are unchanged
by adding documentation. -/
partial def Documentation.tokens (stx : Syntax) : Array String :=
  if stx.getKind == ``Parser.Command.docComment ||
      stx.getKind == ``Parser.Command.moduleDoc then #[]
  else match stx with
  | .atom _ value => #[value]
  | .ident _ _ name _ => #[name.toString]
  | .node _ kind children =>
      #["(" ++ kind.toString] ++ children.foldl (fun out child => out ++ tokens child) #[] ++ #[")"]
  | .missing => #["<missing>"]

/-- Extract source ranges for actual declarations and explicit structure fields.
Use: `main` exports these ranges for the Python documentation-coverage check;
comments containing apparent `theorem`/`def` keywords cannot create false objects.
Source: Lean.Parser.Command's declaration and structure-binder syntax kinds. -/
partial def Documentation.nodes (stx : Syntax) : Array Json := Id.run do
  let mut out := #[]
  if stx.getKind == ``Parser.Command.declaration ||
      (stx.getArgs.size > 0 &&
        ["lemma", "Mathlib.Tactic.lemma"].contains stx.getKind.toString) ||
      [``Parser.Command.structSimpleBinder, ``Parser.Command.structExplicitBinder,
       ``Parser.Command.structImplicitBinder, ``Parser.Command.structInstBinder].contains
        stx.getKind then
    if let some start := stx.getPos? then
      if let some finish := stx.getTailPos? then
        out := out.push <| Json.mkObj [
          ("kind", toJson (if ["lemma", "Mathlib.Tactic.lemma"].contains stx.getKind.toString then
            "Lean.Parser.Command.declaration" else stx.getKind.toString)),
          ("start", toJson start.byteIdx),
          ("end", toJson finish.byteIdx), ("tokens", toJson (tokens stx))]
  for child in stx.getArgs do out := out ++ nodes child
  return out

/-- Validate exact fully qualified article references quoted in source comments.
Use: `main` checks references against the actual imported declaration/module names.
Expressions containing spaces or mathematical operators are left to the syntax/token
comparison; this routine checks standalone names, including private dependencies.
Source: Lean.Environment's constant map and imported-module header. -/
def Documentation.checkReferences (known : Std.HashSet String) (path source : String) : IO Unit := do
  for quoted in source.splitOn "`" do
    let article := quoted.startsWith "«2606.16671v2»." ||
      quoted.startsWith "«2610.05164v2»." || quoted.startsWith "_private.«2606.16671v2»." ||
      quoted.startsWith "_private.«2610.05164v2»."
    let identifier := quoted.toList.all fun c =>
      c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '«' || c == '»'
    if article && identifier && !known.contains quoted then
      throw <| IO.userError s!"Unknown article reference in {path}: {quoted}"

/-- Parse the supplied source list using the existing compiled environment.
The input JSON lists `(path, open namespaces)` pairs; the output records declaration
ranges. Activating each file's own notation scopes avoids enabling incompatible
notation from unrelated modules. If a baseline directory is supplied, compare
parsed executable tokens file by file and fail on any difference.
Use: the optional parser mode of `Scripts/CheckDocumentation.py` for both articles.
Source: Lean's standard parser and imported syntax extensions. The unsafe qualifier
permits loading those extensions; it creates no mathematical proof or axiom. -/
unsafe def main (args : List String) : IO Unit := do
  unless args.length == 2 || args.length == 3 do
    throw <| IO.userError "Expected input JSON, output JSON, and optional baseline directory"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let environment ← importModules (loadExts := true)
    #[{ module := `PolynomialRealizationsProgram }] {}
  let mut known : Std.HashSet String := {}
  for (name, _) in environment.constants.toList do
    known := known.insert name.toString
  for name in environment.header.moduleNames do
    known := known.insert name.toString
  let input ← IO.FS.readFile args[0]!
  let paths : Array (String × Array String) ←
    IO.ofExcept (Json.parse input >>= fromJson?)
  let mut output := #[]
  for (path, scopes) in paths do
    let environment := scopes.foldl
      (fun env name => Parser.parserExtension.activateScoped env name.toName) environment
    let current ← Parser.testParseFile environment (System.FilePath.mk path)
    Documentation.checkReferences known path (← IO.FS.readFile path)
    if let some baseline := args[2]? then
      let previous ← Parser.testParseFile environment ((System.FilePath.mk baseline) / path)
      unless Documentation.tokens previous == Documentation.tokens current do
        throw <| IO.userError s!"Executable tokens changed: {path}"
    output := output.push <| Json.mkObj [
      ("path", toJson path), ("declarations", toJson (Documentation.nodes current))]
  IO.FS.writeFile args[1]! (Json.arr output).compress
  IO.println s!"Parsed {paths.size} sources successfully."
