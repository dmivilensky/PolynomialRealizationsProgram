"""Receive the pinned Part II mathematical archive and generate local Lean inputs.

Only bounded JSON is read from the supplier. The local converters propose
ordinary Lean declarations; subsequent strict compilation and kernel replay
verify their mathematics.
"""
import argparse
import hashlib
from importlib import import_module
import json
from pathlib import Path
import tempfile

from .FetchCertificate import ROOT, fetch, load_source, verify_archive
from .PolyakPartII.Payload import read_archive
from .PolyakPartIIOutputs import EXPECTED

MODULES = [("trigonometry", "Trig"), ("rational", "Rational"),
           ("exact313", "Exact313"), ("plateaus", "Plateaus"),
           ("plateaus", "PlateauSymbol"), ("plateaus", "PlateauCoefficients"),
           ("plateaus", "PlateauPrimal"),
           ("system313", "System313")]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tools():
    folder = Path(__file__).with_name("PolyakPartII")
    paths = [Path(__file__), Path(__file__).with_name("PolyakPartIIOutputs.py"),
             *sorted(folder.rglob("*.py"))]
    return {str(path.relative_to(ROOT)): digest(path) for path in paths}


def cached(receipt, root, source, generators):
    try:
        record = json.loads(receipt.read_text())
        outputs = record["generated_sha256"]
        return (record["schema"] == "polyak-part2-preparation-v1"
                and record["archive_sha256"] == source["archive_sha256"]
                and record["tool_sha256"] == generators
                and isinstance(outputs, dict) and set(outputs) == EXPECTED
                and all((root / name).is_file() and digest(root / name) == value
                        for name, value in outputs.items()))
    except (OSError, ValueError, KeyError, TypeError):
        return False


def prepare(source_path, archive=None, root=ROOT, offline=False, check=False):
    root = Path(root).resolve()
    source = load_source(Path(source_path))
    if (source.get("transport") != "local" or
            source["archive_path"] != "polyak-code/part2/proof/proof.tar.xz"):
        raise ValueError("Unexpected Part II mathematical data supplier")
    cache = ROOT / ".lake/certificates/polyak/PartII"
    if archive is None:
        archive = Path(fetch(source, cache, offline=offline)["archive"])
    else:
        archive = Path(archive).resolve()
        verify_archive(archive, source)
    folder = cache / source["archive_sha256"]
    folder.mkdir(parents=True, exist_ok=True)
    receipt = folder / "preparation.json"
    generators = tools()
    if cached(receipt, root, source, generators):
        return {"prepared": True, "cached": True, "generated_files": len(EXPECTED),
                "scope": "part2", "mathematics": "requires the subsequent Lean check"}
    payload = read_archive(archive)
    hashes, changed = {}, []
    with tempfile.TemporaryDirectory(prefix="part2-inputs-", dir=folder) as temporary:
        staging = Path(temporary)
        generated = []
        for group, module in MODULES:
            converter = import_module(".PolyakPartII." + module, __package__)
            files = converter.generate(payload["groups"][group], staging)
            if set(files) != converter.OUTPUTS:
                raise ValueError("Local converter output contract differs: " + module)
            generated.extend(files)
        if len(generated) != len(EXPECTED) or set(generated) != EXPECTED:
            raise ValueError("Part II converters changed the allowed generated output set")
        # The entire generation is complete before the first installation.
        for name in sorted(EXPECTED):
            raw = (staging / name).read_bytes()
            hashes[name] = hashlib.sha256(raw).hexdigest()
            if not (root / name).is_file() or (root / name).read_bytes() != raw:
                changed.append(name)
        if check and changed:
            raise ValueError("Part II generated inputs differ: " + ", ".join(changed))
        if not check:
            for name in changed:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(dir=target.parent, prefix=".proposal-", delete=False) as handle:
                    proposed = Path(handle.name)
                    handle.write((staging / name).read_bytes())
                try:
                    proposed.replace(target)
                finally:
                    proposed.unlink(missing_ok=True)
    receipt.write_text(json.dumps({"schema": "polyak-part2-preparation-v1",
                                  "archive_sha256": source["archive_sha256"],
                                  "tool_sha256": generators, "generated_sha256": hashes,
                                  "source_identity_only": True,
                                  "lean_verification_required": True}, sort_keys=True, indent=2) + "\n")
    return {"prepared": True, "cached": False, "generated_files": len(EXPECTED),
            "changed_files": len(changed), "scope": "part2", "check_only": check,
            "mathematics": "requires the subsequent Lean check"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / "polyak/Certificates/PartII/Source.json")
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        print(json.dumps(prepare(args.source, args.archive, args.root, args.offline, args.check), sort_keys=True))
    except (OSError, ValueError, KeyError, RuntimeError, ImportError) as error:
        parser.exit(1, f"Polyak Part II preparation failed: {error}\n")


if __name__ == "__main__":
    main()
