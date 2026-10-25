"""Recompute the selected exact witnesses and automatically package proof.tar.xz."""
import argparse
import hashlib
from importlib import import_module
import io
import json
from pathlib import Path
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "HEAVY_BALL_PARTII_PROOF_DATA"
SCHEMA = "heavy-ball-part2-proof-v1"
GROUPS = ("rational", "exact313", "plateaus", "trigonometry", "system313")


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + "\n").encode()


def regenerate(destination=None):
    """Build all witnesses from formulas, then install a deterministic JSON archive."""
    if not __debug__:
        raise RuntimeError("Do not generate witnesses with python -O")
    destination = Path(destination or ROOT / "part2/proof")
    raw = {}
    for group in GROUPS:
        module = import_module("." + group, __package__)
        builder = getattr(module, "build_payload", None) or module.generate
        data = builder()
        raw[group + ".json"] = encode({"schema": SCHEMA, "kind": group, "data": data})
        print("Generated", group, len(raw[group + ".json"]), "bytes", flush=True)
    manifest = {"format": FORMAT, "version": 1, "schema": SCHEMA,
                "members": {name: {"bytes": len(value),
                                   "sha256": hashlib.sha256(value).hexdigest()}
                            for name, value in sorted(raw.items())}}
    raw["manifest.json"] = encode(manifest)
    destination.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="part2-proof-", dir=destination) as temporary:
        archive = Path(temporary) / "proof.tar.xz"
        with tarfile.open(archive, "w:xz", format=tarfile.USTAR_FORMAT) as stream:
            for name, value in sorted(raw.items()):
                member = tarfile.TarInfo(name)
                member.size = len(value)
                member.mode = 0o644
                member.mtime = member.uid = member.gid = 0
                stream.addfile(member, io.BytesIO(value))
        digest = hashlib.sha256(archive.read_bytes()).hexdigest()
        size = archive.stat().st_size
        archive.replace(destination / "proof.tar.xz")
    (destination / "manifest.json").write_bytes(raw["manifest.json"])
    return {"archive": str(destination / "proof.tar.xz"), "archive_bytes": size,
            "archive_sha256": digest, "groups": list(GROUPS)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", choices=("regen",), default="regen")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    print(json.dumps(regenerate(args.output), sort_keys=True))


if __name__ == "__main__":
    main()
