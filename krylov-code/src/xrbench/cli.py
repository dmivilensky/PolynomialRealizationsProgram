"""Small CLI; rendering never runs optimization, resume never mixes code."""

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path


def main():
    cache = Path(tempfile.gettempdir()) / "xrbench-cache"
    os.environ.setdefault("MPLCONFIGDIR", str(cache / "matplotlib"))
    os.environ.setdefault("XDG_CACHE_HOME", str(cache))
    parser = argparse.ArgumentParser(prog="xrbench")
    sub = parser.add_subparsers(dest="action", required=True)
    for name in ["plan", "run"]:
        p = sub.add_parser(name)
        p.add_argument("--output", type=Path, default=Path("artifacts/full"))
        p.add_argument("--pilot", action="store_true")
        p.add_argument("--workers", type=int, default=8)
        p.add_argument("--budget", type=int, default=100000)
        p.add_argument("--max-time", type=float, default=120.0)
        p.add_argument("--libsvm", action="store_true", help="Include the frozen 24 logistic objectives")
        p.add_argument("--libsvm-time", type=float, default=300.0)
    for name in ["resume", "render", "status"]:
        p = sub.add_parser(name)
        p.add_argument("--output", type=Path, default=Path("artifacts/full"))
    sub.add_parser("_worker")
    a = parser.parse_args()
    from xrbench.campaign import (
        execute,
        freeze_implementation_metadata,
        make_manifest,
        materialize_aliases,
        read_history,
        run_job,
        validate_history,
    )

    if a.action == "_worker":
        print("XR_RESULT " + json.dumps(run_job(json.load(sys.stdin)), allow_nan=False), flush=True)
        return
    if a.action in ["plan", "run"]:
        m = make_manifest(a.budget, a.max_time, a.workers, a.pilot,
                          include_libsvm=a.libsvm, libsvm_time=a.libsvm_time)
        if a.action == "plan":
            print(
                json.dumps(
                    {k: v for k, v in m.items() if k not in ["jobs", "problems", "aliases"]},
                    indent=2,
                )
            )
            print(
                f"{len(m['problems'])} problem contexts; {len(m['jobs'])} computations; "
                f"{len(m.get('aliases', []))} comparison aliases"
            )
            return
        rows, m = execute(a.output, freeze_implementation_metadata(m))
    else:
        m = json.loads((a.output / "manifest.json").read_text())
        if a.action == "resume":
            rows, m = execute(a.output)
        else:
            rows = read_history(a.output / "history.jsonl")
            validate_history(rows, m)
            rows = materialize_aliases(rows, m)
        if a.action == "status":
            actual = [row for row in rows if not row.get("alias_of")]
            print(
                f"{len(actual)}/{len(m['jobs'])} computations complete; "
                f"{sum(r['success'] for r in actual)} converged; "
                f"{len(rows) - len(actual)}/{len(m.get('aliases', []))} comparison aliases available"
            )
            return
    from xrbench.study import render

    render(rows, a.output, expected_methods=m["methods"], expected_problems=m["problems"])


if __name__ == "__main__":
    main()
