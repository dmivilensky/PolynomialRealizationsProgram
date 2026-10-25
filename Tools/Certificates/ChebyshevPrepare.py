"""Check Chebyshev II witnesses against its pinned external mathematical archive.

The standard verification command acquires the archive, reconstructs the reference
and both quadrature proposals, and compares every installed witness. No supplier
program runs. The subsequent Lean build checks the mathematical certificates.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from .FetchCertificate import ROOT, fetch, load_source, verify_archive

STEPS = (
    ("ReferenceInputs", ("--offline", "--check")),
    ("VerifyResidualBatches", ("--offline", "--check")),
    ("ContactProposals", ("--offline",)),
    ("AmplitudeProposals", ()),
    ("VerifyContact", ("--offline", "--check")),
    ("VerifyAmplitude", ("--offline", "--check")),
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tool_hashes():
    folder = ROOT / "Tools/Certificates"
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(folder.glob("*.py"))
            if not p.name.startswith("Polyak")}


def witness_hashes():
    return {str(p.relative_to(ROOT)): digest(p)
            for p in sorted((ROOT / "chebyshev2/Certificates").rglob("*.lean"))}


def prepare(source_path, archive=None, offline=False):
    source_path = Path(source_path).resolve()
    if source_path != ROOT / "chebyshev2/Certificates/Source.json":
        raise ValueError("Expected the workspace Chebyshev II source descriptor")
    source = load_source(source_path)
    cache = ROOT / ".lake/certificates/chebyshev2"
    if archive is None:
        archive = Path(fetch(source, cache, offline=offline)["archive"])
    else:
        archive = Path(archive).resolve()
        verify_archive(archive, source)
    folder = cache / source["archive_sha256"]
    folder.mkdir(parents=True, exist_ok=True)
    cached_archive = folder / "proof.tar.xz"
    # The individual generators use the same pinned offline archive location.
    if archive != cached_archive:
        with tempfile.NamedTemporaryFile(dir=folder, prefix="archive-", delete=False) as f:
            staged = Path(f.name)
        try:
            shutil.copyfile(archive, staged)
            verify_archive(staged, source)
            staged.replace(cached_archive)
        finally:
            staged.unlink(missing_ok=True)
    verify_archive(cached_archive, source)
    identity = {"schema": "chebyshev2-preparation-v1",
                "source_sha256": digest(source_path),
                "archive_sha256": source["archive_sha256"],
                "tools_sha256": tool_hashes()}
    receipt = folder / "preparation.json"
    witnesses = witness_hashes()
    try:
        previous = json.loads(receipt.read_text())
        if (witnesses and all(previous.get(k) == v for k, v in identity.items())
                and previous.get("witness_sha256") == witnesses):
            return {"prepared": True, "cached": True, "witness_files": len(witnesses)}
    except (OSError, ValueError, TypeError):
        pass
    logs = folder / "preparation"
    logs.mkdir(exist_ok=True)
    for module, arguments in STEPS:
        print(f"chebyshev2: reconstructing {module}", flush=True)
        log_path = logs / (module + ".log")
        with log_path.open("w") as log:
            result = subprocess.run(
                [sys.executable, "-B", "-m", "Tools.Certificates." + module, *arguments],
                cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            raise ValueError(f"Chebyshev II witness reconstruction failed: {module}; see {log_path}")
    witnesses = witness_hashes()
    if not witnesses:
        raise ValueError("Chebyshev II certificate witnesses are missing")
    if digest(source_path) != identity["source_sha256"] or tool_hashes() != identity["tools_sha256"]:
        raise ValueError("Chebyshev II source or generators changed during preparation")
    receipt.write_text(json.dumps({**identity, "witness_sha256": witnesses}, indent=2) + "\n")
    return {"prepared": True, "cached": False, "witness_files": len(witnesses)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / "chebyshev2/Certificates/Source.json")
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--offline", action="store_true")
    args = parser.parse_args()
    try:
        print(json.dumps(prepare(args.source, args.archive, args.offline)), flush=True)
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f"Chebyshev II preparation failed: {error}\n")


if __name__ == "__main__":
    main()
