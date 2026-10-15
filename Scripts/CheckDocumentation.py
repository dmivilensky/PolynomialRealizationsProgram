"""Check declaration/field/proof documentation and generator docstrings.

The default pass works from source only, including after distribution cleanup.
--parse additionally uses Lean's parser and the existing compiled environment;
--baseline DIR compares parsed executable tokens with a saved pre-edit source tree.
Generated literal witnesses and their deterministic assembly files are exempt from
object-level prose; their generators and analytic soundness bridges remain checked.
"""
import argparse
import ast
from bisect import bisect_right
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
PAPERS = ("2606.16671v2", "2610.05164v2")
GENERATED = {"ReferenceResidualShared.lean", "ReferenceResidualData.lean",
             "ReferenceResiduals.lean", "ContactShared.lean", "AmplitudeShared.lean",
             "Reference.lean", "ReferenceModel.lean", "ReferenceTrajectoryIndex.lean"}


def generated(path):
    """
    Identify repeated witness sources/assembly, not their analytic proof bridges.

    Data/Batch modules contain literal panels and kernel decision proofs; Correspondence
    modules perform the same panel-to-actual-model assembly per row. Their common soundness
    rules are documented in the handwritten modules.
    """
    return "Certificates" in path.parts and (
        any(part.endswith("Batches") for part in path.parts) or path.name in GENERATED)


def lean_sources():
    """
    List owned sources only; dependency caches and Git internals are excluded.
    """
    return sorted([*ROOT.glob("*.lean"), *(path for folder in (*PAPERS,
                  "PolynomialRealizationsProgram", "Scripts")
                  for path in (ROOT / folder).rglob("*.lean"))])


def lexical_source(source):
    """
    Mask comments/strings with spaces and retain source-positioned prose blocks.

    Nested Lean block comments and escaped string quotes are handled explicitly. Keeping
    newlines/character positions lets the coverage pass locate declarations without confusing
    quoted/generated Lean code with actual declarations.
    """
    masked = list(source)
    blocks = []
    i = 0
    while i < len(source):
        if source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            blocks.append((i, end, "line", source[i + 2:end]))
        elif source.startswith("/-", i):
            kind = "doc" if source.startswith("/--", i) else "module" if source.startswith("/-!", i) else "block"
            end = i + 2
            depth = 1
            while depth and end < len(source):
                if source.startswith("/-", end):
                    depth += 1
                    end += 2
                elif source.startswith("-/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            if depth:
                raise ValueError("Unterminated Lean block comment")
            blocks.append((i, end, kind, source[i + 3:end - 2] if kind in ("doc", "module") else source[i + 2:end - 2]))
        elif source[i] == '"':
            end = i + 1
            while end < len(source):
                if source[end] == "\\":
                    end += 2
                elif source[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
        else:
            i += 1
            continue
        for j in range(i, min(end, len(source))):
            if source[j] != "\n":
                masked[j] = " "
        i = end
    return "".join(masked), blocks


def adjacent_doc(start, code, blocks):
    """
    Find the nearest declaration/field doc with no intervening executable text.
    """
    ends = [block[1] for block in blocks]
    index = bisect_right(ends, start) - 1
    if index >= 0:
        block = blocks[index]
        if block[2] in ("doc", "block") and not code[block[1]:start].strip():
            return block
    return None


def check_file(path, parsed=None):
    """
    Require object prose, proof roles/article chains and meaningful proof notes.

    With parser output, declaration positions come from Lean itself. The source-only fallback
    recognizes declaration commands, while field coverage is restricted to structure bodies.
    Generated witnesses are inspected elsewhere for module coverage.
    """
    source = path.read_text()
    code, blocks = lexical_source(source)
    if generated(path):
        return 0, 0, 0
    pattern = r"^[ \t]*(?:@\[[^\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)[ \t]+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|example|elab)\b"
    commands = list(re.finditer(pattern, code, re.M))
    count = 0
    fields = 0
    constructors = 0
    for index, command in enumerate(commands):
        kind = command[1]
        start = command.start()
        finish = commands[index + 1].start() if index + 1 < len(commands) else len(source)
        doc = adjacent_doc(start, code, blocks)
        if not doc:
            raise ValueError(f"Undocumented {kind}: {path.relative_to(ROOT)}:{source.count(chr(10), 0, start) + 1}")
        prose = doc[3]
        if len(prose.split()) < 8:
            raise ValueError(f"Insufficient object explanation: {path.relative_to(ROOT)}:{start}")
        if path.parts[-2] not in ("Scripts", "PolynomialRealizationsProgram"):
            if "Use:" not in prose or not re.search(r"Article(?: chain)?:", prose):
                raise ValueError(f"Missing object role/article chain: {path.relative_to(ROOT)}:{start}")
        if kind in ("theorem", "lemma", "example") and "Proof:" not in prose:
            raise ValueError(f"Missing proof explanation: {path.relative_to(ROOT)}:{start}")
        proof = re.search(r":=[ \t]*by\b", code[start:finish])
        if proof and kind in ("theorem", "lemma", "example"):
            proof_start = start + proof.end()
            lines = []
            for line in code[proof_start:finish].splitlines():
                if line.strip() and not line[0].isspace():
                    break
                if line.strip():
                    lines.append(line)
            if len(lines) >= 9 and not any(block[2] == "line" and
                                         proof_start <= block[0] < finish for block in blocks):
                raise ValueError(f"Long proof needs mathematical step comments: {path.relative_to(ROOT)}:{start}")
        count += 1
        if kind in ("structure", "class"):
            body = code[start:finish]
            for field in re.finditer(r"^[ \t]+([\w'₀-₉]+)[ \t]*(?:\([^\n]*?\)[ \t]*)*:[^=]", body, re.M):
                position = start + field.start()
                if not adjacent_doc(position, code, blocks):
                    raise ValueError(f"Undocumented structure field {field[1]}: {path.relative_to(ROOT)}")
                fields += 1
        if kind == "inductive":
            for constructor in re.finditer(r"^[ \t]*\|[ \t]*([\w'₀-₉]+)\b", code[start:finish], re.M):
                position = start + constructor.start()
                if not adjacent_doc(position, code, blocks):
                    raise ValueError(f"Undocumented constructor {constructor[1]}: {path.relative_to(ROOT)}")
                constructors += 1
    if parsed is not None:
        actual = sum(item["kind"].endswith("declaration") for item in parsed)
        # elab is a parser command, not a Command.declaration node.
        expected = sum(command[1] != "elab" for command in commands)
        if actual != expected:
            raise ValueError(f"Lexical/parser declaration counts differ: {path.relative_to(ROOT)}: {expected}/{actual}")
    return count, fields, constructors


def check_python():
    """
    Require prose on every Python module, class, function and nested helper.
    """
    count = 0
    for path in (ROOT / "Scripts").glob("*.py"):
        tree = ast.parse(path.read_text(), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
                if not ast.get_docstring(node):
                    raise ValueError(f"Undocumented Python object: {path.name}:{getattr(node, 'lineno', 1)}")
                count += 1
    return count


def parser_index(paths, baseline):
    """
    Run the optional Lean parser once for all handwritten sources.

    Runtime parser extensions are loaded from existing compiled modules; Lake is never asked to
    rebuild proofs. Inputs/outputs are temporary and automatically removed. A baseline compares
    only files present in that saved source tree.
    """
    selected = [path for path in paths if not generated(path)]
    if baseline:
        selected = [path for path in selected if (baseline / path.relative_to(ROOT)).exists()]
    records = []
    for path in selected:
        scopes = []
        for match in re.finditer(r"^open (?:scoped )?([^\n]+)", path.read_text(), re.M):
            scopes.extend(name for name in match[1].split()
                          if re.fullmatch(r"[A-Za-z][A-Za-z0-9_.]*", name) and name != "in")
        if "IntervalExpr" in scopes:
            scopes.append("LeanCert.Core.IntervalExpr")
        records.append([str(path.relative_to(ROOT)), scopes])
    with tempfile.TemporaryDirectory() as temporary:
        folder = Path(temporary)
        input_path, output_path = folder / "input.json", folder / "output.json"
        input_path.write_text(json.dumps(records))
        command = ["lake", "env", "lean", "--run", "Scripts/InspectDocumentation.lean",
                   str(input_path), str(output_path)]
        if baseline:
            command.append(str(baseline.resolve()))
        subprocess.run(command, cwd=ROOT, check=True)
        return {record["path"]: record["declarations"] for record in json.loads(output_path.read_text())}


def main():
    """
    Check all source documentation, optionally with exact Lean syntax inspection.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parse", action="store_true", help="Use existing compiled modules for Lean parser validation")
    parser.add_argument("--baseline", type=Path, help="Compare parsed executable tokens with a pre-edit source tree")
    args = parser.parse_args()
    paths = lean_sources()
    parsed = parser_index(paths, args.baseline) if args.parse or args.baseline else {}
    objects = fields = constructors = 0
    for path in paths:
        obj, fld, ctor = check_file(path, parsed.get(str(path.relative_to(ROOT))))
        objects += obj
        fields += fld
        constructors += ctor
    python = check_python()
    print(f"Documentation: {objects} Lean declarations, {fields} fields, "
          f"{constructors} constructors, {python} Python objects; all checked.")


if __name__ == "__main__":
    main()
