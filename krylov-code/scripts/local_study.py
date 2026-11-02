#!/usr/bin/env python3
"""Dense accepted-iterate diagnostics of the unchanged full-memory XR solvers.

This is a local accuracy experiment, not another CUTEst comparison. The exact
Hessian at the known minimizer defines the diagnostic norm; it is never passed
to a solver. Every accepted iterate is retained. In particular, rejected probes
cannot satisfy this experiment's target. Its extra diagnostic work is excluded
from the competitive timing profiles.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
for _name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
              "VECLIB_MAXIMUM_THREADS", "BLIS_NUM_THREADS"):
    os.environ[_name] = "1"


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def manifest():
    from xrbench.campaign import environment, source_hash

    return dict(
        schema="xr-dense-local-v1", source_hash=source_hash(),
        script_sha256=file_hash(__file__), environment=environment(),
        dimensions=[5, 10, 20], condition_numbers=[10., 100.], seeds=list(range(10)),
        arithmetic="IEEE binary64; exact analytic H* used only for diagnostics",
        epsilon=.1, initial_base_energy=.03, target=1e-12,
        max_accepted=300, budget=3000, max_time=30.,
        methods=["XR", "XR-F"],
        error="sqrt(x.T @ (A + epsilon*Ac@Ac.T) @ x), divided by its initial value",
        sample="Every actual accepted iterate, including the initial point; no subsampling.",
        stopping="Accepted-iterate H*-energy ratio <= 1e-12; probes do not satisfy the target.",
        timing="Diagnostic only: not pooled with competitive wall-clock observations.",
        selection="Complete Cartesian product, fixed before running; no seed selection.",
    )


def run_one(n, kappa, seed, method, config):
    import numpy as np

    from xrbench.methods.xr_native import solve
    from xrbench.oracle import Budget, Oracle
    from xrbench.problems.synthetic import SmoothQuadratic

    class TargetReached(Exception):
        pass

    class IterationLimit(Exception):
        pass

    problem = SmoothQuadratic(n, kappa, config["epsilon"], seed, local=True)
    hessian = problem.A + problem.epsilon * problem.Ac @ problem.Ac.T
    error = lambda x: float(np.sqrt(max(0., float(x @ hessian @ x))))
    initial = error(problem.x0)
    oracle = Oracle(problem, budget=config["budget"], max_time=config["max_time"])
    _, gradient = oracle.fg(problem.x0)
    points = [dict(iteration=0, n_g=oracle.n_g_evals, n_f=oracle.n_f_evals,
                   error=1., gnorm=float(np.linalg.norm(gradient)),
                   window_used=None, full_window=False, counters={"nsafe": 0})]

    def accepted(point, _value, gradient, info):
        window = info["window"]
        points.append(dict(
            iteration=info["iteration"], n_g=oracle.n_g_evals, n_f=oracle.n_f_evals,
            error=error(point) / initial, gnorm=float(np.linalg.norm(gradient)),
            window_used=window, full_window=window == n,
            counters=dict(info["counters"]),
        ))
        if points[-1]["error"] <= config["target"]:
            raise TargetReached()
        if points[-1]["iteration"] >= config["max_accepted"]:
            raise IterationLimit()

    status = "method_stop"
    try:
        solve(oracle, problem.x0, m0=n, m_max=n, values=method == "XR-F",
              accepted_hook=accepted)
    except TargetReached:
        status = "converged"
    except IterationLimit:
        status = "iteration_limit"
    except Budget:
        status = oracle.status
    full = next((p["n_g"] for p in points if p["full_window"]), None)
    return dict(
        method=method, n=n, kappa=kappa, seed=seed, epsilon=config["epsilon"],
        status=status, success=status == "converged", n_g=oracle.n_g_evals,
        n_f=oracle.n_f_evals, accepted=len(points) - 1, first_full_n_g=full,
        trace=points, counters=dict(oracle.info.get("counters", {})), initial_energy=initial,
        source_hash=config["source_hash"], backend="native-c",
    )


def validate(config, rows):
    from xrbench.campaign import source_hash

    if config["source_hash"] != source_hash() or config["script_sha256"] != file_hash(__file__):
        raise ValueError("Frozen local-study source changed; use a new output directory")
    expected = {(n, k, s, m) for n in config["dimensions"] for k in config["condition_numbers"]
                for s in config["seeds"] for m in config["methods"]}
    keys = [(r["n"], r["kappa"], r["seed"], r["method"]) for r in rows]
    if len(keys) != len(set(keys)) or not set(keys) <= expected:
        raise ValueError("Duplicate or unexpected local-study observation")
    for row in rows:
        if row["source_hash"] != config["source_hash"]:
            raise ValueError("Local-study producer changed")
        trace = row["trace"]
        if [p["iteration"] for p in trace] != list(range(len(trace))):
            raise ValueError("An accepted iterate was skipped")
    return expected - set(keys)


def render(output, config, rows):
    from xrbench.study import render_local_study

    missing = validate(config, rows)
    if missing:
        raise ValueError(f"Incomplete local study: {len(missing)} missing observations")
    return render_local_study(rows, output, config)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["run", "render"])
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/local")
    args = parser.parse_args()
    output = args.output.resolve()
    logs = output / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    path = logs / "manifest.json"
    if path.exists():
        config = json.loads(path.read_text())
    else:
        if args.action == "render":
            raise ValueError("No local-study manifest")
        config = manifest()
        path.write_text(json.dumps(config, indent=2) + "\n")
    history = logs / "history.jsonl"
    from xrbench.campaign import recover_history_tail

    recover_history_tail(history)
    rows = [json.loads(line) for line in history.read_text().splitlines()] if history.exists() else []
    missing = validate(config, rows)
    if args.action == "run":
        with history.open("a") as stream:
            for n, kappa, seed, method in sorted(missing):
                row = run_one(n, kappa, seed, method, config)
                stream.write(json.dumps(row, allow_nan=False) + "\n")
                stream.flush()
                os.fsync(stream.fileno())
                rows.append(row)
                print(f"{len(rows)}/120 n={n} kappa={kappa:g} seed={seed} {method}: "
                      f"{row['status']}, {row['n_g']} gradients", flush=True)
    render(output, config, rows)


if __name__ == "__main__":
    main()
