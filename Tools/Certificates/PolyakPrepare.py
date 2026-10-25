"""Receive pinned external mathematical data and prepare local Polyak Lean inputs.

The external producer supplies JSON only. All Python that generates Lean lives
in this workspace, and only Lean's subsequent build accepts mathematical claims.
Tools.Verification.Check invokes it through Tools.Certificates.Registry;
Source.json specifies only the external archive location and byte identity.
"""
import argparse
import contextlib
import hashlib
import json
from pathlib import Path
import tempfile

from .FetchCertificate import ROOT, fetch, load_source, verify_archive
from .Polyak.Payload import configure
from ..Verification.CertificateEnvironment import current_matches, pinned_requirements

from .PolyakOutputs import EXPECTED


def _hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tools():
    folder = Path(__file__).with_name("Polyak")
    paths = [Path(__file__), Path(__file__).with_name("PolyakOutputs.py"),
             *sorted(folder.rglob("*.py")), folder / "requirements.txt"]
    return {str(path.relative_to(ROOT)): _hash(path) for path in paths}


def _cached(receipt, root, source, tools):
    """Reuse generation only if the archive, tools and every output still match."""
    try:
        record = json.loads(receipt.read_text())
        if not isinstance(record, dict):
            return False
        generated = record.get("generated_sha256")
        return (record.get("schema") == "polyak-source-preparation-v1" and
                record.get("archive_sha256") == source["archive_sha256"] and
                record.get("tool_sha256") == tools and
                isinstance(generated, dict) and set(generated) == EXPECTED and
                all((root / name).is_file() and _hash(root / name) == digest
                    for name, digest in generated.items()))
    except (OSError, ValueError, TypeError):
        return False


def prepare(source_path, archive=None, root=ROOT, offline=False, check=False):
    """Generate in isolation, then install only the contracted local literal files."""
    root = Path(root).resolve()
    source = load_source(Path(source_path))
    if (source.get("transport") != "local" or
            source["archive_path"] != "polyak-code/part1/proof/proof.tar.xz"):
        raise ValueError("unexpected mathematical data supplier")
    requirements, _, pins = pinned_requirements(ROOT, "Tools/Certificates/Polyak/requirements.txt")
    if not current_matches(pins):
        raise ValueError("this Python does not have the exact generator versions from "
                         f"{requirements}; use python3 -m Tools.Verification.Check polyak "
                         "to prepare its environment, or install those exact pins here")
    cache = ROOT / ".lake" / "certificates" / "polyak"
    if archive is None:
        archive = Path(fetch(source, cache, offline=offline)["archive"])
    else:
        archive = Path(archive).resolve()
        verify_archive(archive, source)
    folder = cache / source["archive_sha256"]
    folder.mkdir(parents=True, exist_ok=True)
    receipt = folder / "preparation.json"
    tools = _tools()
    if _cached(receipt, root, source, tools):
        return {"prepared": True, "cached": True, "generated_files": len(EXPECTED),
                "mathematics": "requires the subsequent Lean check"}
    payload = configure(archive)
    changed = []
    generated_hashes = {}
    from .Polyak import generate_all
    with tempfile.TemporaryDirectory(prefix="polyak-inputs-", dir=folder) as temporary:
        staging = Path(temporary)
        with (folder / "generation.log").open("w") as log, contextlib.redirect_stdout(log):
            generated = generate_all(staging)
        if len(generated) != len(EXPECTED) or set(generated) != EXPECTED:
            raise ValueError("local generators changed the contracted output set")
        for name in sorted(EXPECTED):
            proposed, target = staging / name, root / name
            raw = proposed.read_bytes()
            generated_hashes[name] = hashlib.sha256(raw).hexdigest()
            if not target.is_file() or target.read_bytes() != raw:
                changed.append(name)
        if check and changed:
            raise ValueError("generated Lean sources differ: " + ", ".join(changed))
        if not check:
            for name in changed:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(dir=target.parent, prefix=".proposal-",
                                                 delete=False) as handle:
                    temporary_target = Path(handle.name)
                    handle.write((staging / name).read_bytes())
                try:
                    temporary_target.replace(target)
                finally:
                    temporary_target.unlink(missing_ok=True)
    # Cache only JSON, to support later formal continuation without upstream code.
    data = folder / "payload"
    data.mkdir(exist_ok=True)
    for name, raw in payload["raw"].items():
        (data / name).write_bytes(raw)
    record = {"schema": "polyak-source-preparation-v1",
              "archive_sha256": source["archive_sha256"], "tool_sha256": tools,
              "generator_versions": pins,
              "generated_sha256": generated_hashes,
              "source_identity_only": True, "lean_verification_required": True}
    receipt.write_text(json.dumps(record, sort_keys=True, indent=2) + "\n")
    return {"prepared": True, "cached": False, "generated_files": len(EXPECTED),
            "changed_files": len(changed), "check_only": check,
            "mathematics": "requires the subsequent Lean check"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / "polyak/Certificates/Source.json")
    parser.add_argument("--archive", type=Path,
                        help="explicit local archive, still checked against Source.json")
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--check", action="store_true", help="compare generated sources without replacing them")
    args = parser.parse_args()
    try:
        result = prepare(args.source, args.archive, args.root, args.offline, args.check)
    except (OSError, ValueError, KeyError, RuntimeError, ImportError) as error:
        parser.exit(1, f"Polyak source preparation failed: {error}\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
