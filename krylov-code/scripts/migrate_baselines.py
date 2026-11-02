#!/usr/bin/env python3
"""Explicitly seed a new campaign with source-identical CUTEst baselines.

No optimization is performed. Every producer source-file map is verified, and
all mathematical dependencies and execution inputs must match. Existing output
is never overwritten. This utility is deliberately separate from normal run
and resume: changed solvers cannot silently inherit old measurements.
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))


def main():
    from xrbench.campaign import (
        digest,
        make_manifest,
        read_history,
        reuse_cutest_baselines,
        validate_history,
    )

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--previous", type=Path, required=True, help="Archived campaign folder")
    parser.add_argument("--output", type=Path, required=True, help="New, empty campaign folder")
    parser.add_argument(
        "--producer-map",
        type=Path,
        action="append",
        default=[],
        help="Explicit source-file JSON map for an earlier producer; repeatable",
    )
    parser.add_argument("--budget", type=int, default=100000)
    parser.add_argument("--seconds", type=float, default=120.0)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument(
        "--dry-run", action="store_true", help="Validate and report without writing"
    )
    args = parser.parse_args()
    previous_path = args.previous / "manifest.json"
    history_path = args.previous / "history.jsonl"
    previous = json.loads(previous_path.read_text())
    maps = {}
    for path in args.producer_map:
        files = json.loads(path.read_text())
        maps[digest(files)] = files
    manifest, rows = reuse_cutest_baselines(
        previous,
        read_history(history_path),
        make_manifest(args.budget, args.seconds, args.workers),
        producer_maps=maps,
    )
    manifest["baseline_reuse"].update(
        prior_manifest_sha256=hashlib.sha256(previous_path.read_bytes()).hexdigest(),
        prior_history_sha256=hashlib.sha256(history_path.read_bytes()).hexdigest(),
    )
    validate_history(rows, manifest)
    print(
        f"Verified {len(rows)} unchanged CUTEst baseline observations; "
        f"{len(manifest['jobs']) - len(rows)} new computations; "
        f"{len(manifest['aliases'])} declared comparison aliases."
    )
    if args.dry_run:
        return
    if args.output.exists() and any(args.output.iterdir()):
        raise ValueError("Migration output must be empty; never overwrite a frozen campaign")
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    with (args.output / "history.jsonl").open("w") as stream:
        for row in rows:
            stream.write(json.dumps(row, separators=(",", ":"), allow_nan=False) + "\n")


if __name__ == "__main__":
    main()
