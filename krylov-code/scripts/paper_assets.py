#!/usr/bin/env python3
"""Copy the figures and tables used by krylov.tex from a completed study."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ASSETS = {
    "figures/controlled.pdf": "full/figures/controlled.pdf",
    "figures/cutest_gradients.pdf": "full/figures/cutest_gradients.pdf",
    "figures/cutest_time.pdf": "full/figures/cutest_time.pdf",
    "figures/libsvm.pdf": "full/figures/libsvm.pdf",
    "figures/local.pdf": "local/figures/local.pdf",
    "tables/ablations.tex": "full/tables/ablations.tex",
    "tables/settings_summary.tex": "settings/tables/settings_summary.tex",
    "tables/bfgs_reference.tex": "supplement/tables/bfgs_reference.tex",
    "tables/tighter_target.tex": "supplement/tables/tighter_target.tex",
    "tables/local_summary.tex": "local/tables/local_summary.tex",
    "tables/libsvm_datasets.tex": "full/tables/libsvm_datasets.tex",
    "tables/libsvm_comparisons.tex": "full/tables/libsvm_comparisons.tex",
}


def publish(run: Path, output: Path) -> dict:
    """Validate every input before copying; preserve all measured content."""
    checksums = {}
    for target, relative in ASSETS.items():
        source = run / relative
        data = source.read_bytes()
        if source.suffix == ".pdf" and not data.startswith(b"%PDF-"):
            raise ValueError(f"Invalid PDF: {source}")
        if source.suffix == ".tex" and b"\\begin{table}" not in data:
            raise ValueError(f"Invalid table: {source}")
        checksums[target] = hashlib.sha256(data).hexdigest()
    for target, relative in ASSETS.items():
        destination = output / target
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(run / relative, destination)
    return checksums


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, default=ROOT / "artifacts/run")
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/paper")
    args = parser.parse_args()
    print(json.dumps(publish(args.run.resolve(), args.output.resolve()), indent=2))


if __name__ == "__main__":
    main()
