"""Predictions, two Monte Carlo experiments, analysis and two PDF figures.

python run_all.py                     # all, 2048 trials
python run_all.py --trials 256        # same full horizon grid, fewer trials
python run_all.py pred                # predictions only
python run_all.py additive|variation  # one experiment
"""

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np
import predict
import simulate
from common import ADDITIVE, VARIATION, prepare
from models import CoupledCycles, SpikedRidge

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"
KAPPAS = {"additive": (100, 10000), "variation": (10000, 40000)}
HORIZONS = (64, 128, 256, 320, 384, 512, 640, 768, 960, 1024)
CURVE_N = tuple(sorted(set(range(64, 1025, 16)) | set(HORIZONS)))
SIGMA_RELATIVE = 0.3
CHANNEL_RELATIVE = 0.01
SEED = 20261101


def supported(method, N):
    return method != "lf" or not N & (N - 1)


def seed(task, kappa, N):
    text = f"{SEED}|{task}|{kappa}|{N}"
    return int.from_bytes(hashlib.sha256(text.encode()).digest()[:8], "little")


def predictions():
    result = {
        "parameters": {
            "kappas": KAPPAS,
            "horizons": HORIZONS,
            "curve_horizons": CURVE_N,
            "sigma_relative": SIGMA_RELATIVE,
            "channel_relative": CHANNEL_RELATIVE,
            "seed": SEED,
        },
        "additive": {},
        "variation": {},
    }
    for task, methods in [("additive", ADDITIVE), ("variation", VARIATION)]:
        for kappa in KAPPAS[task]:
            problem = SpikedRidge(kappa) if task == "additive" else CoupledCycles(kappa)
            curves = {m: [] for m in methods}
            for N in CURVE_N:
                for method in methods:
                    if not supported(method, N):
                        continue
                    c = prepare(method, N, problem.mu, problem.L)
                    p = (
                        predict.additive(c, problem, SIGMA_RELATIVE * problem.mu)
                        if task == "additive"
                        else predict.variation(c, problem)
                    )
                    curves[method].append(dict(N=N, **predict.serializable(p)))
            result[task][str(kappa)] = curves
            print(f"Predicted {task}, kappa={kappa}", flush=True)
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / "pred.json").write_text(
        json.dumps(result, indent=2, allow_nan=False) + "\n"
    )
    return result


def experiment(task, trials):
    methods = ADDITIVE if task == "additive" else VARIATION
    records = []
    for kappa in KAPPAS[task]:
        problem = SpikedRidge(kappa) if task == "additive" else CoupledCycles(kappa)
        for N in HORIZONS:
            for method in methods:
                if not supported(method, N):
                    continue
                c = prepare(method, N, problem.mu, problem.L)
                if task == "additive":
                    scale = SIGMA_RELATIVE * problem.mu
                    p = predict.additive(c, problem, scale)
                    error, excess, energy = simulate.additive(
                        c, problem, scale, trials, seed(task, kappa, N), p
                    )
                else:
                    scale = CHANNEL_RELATIVE * problem.mu
                    p = predict.variation(c, problem)
                    error, excess, energy = simulate.variation(
                        c, problem, scale, trials, seed(task, kappa, N), p
                    )
                records.append(
                    {
                        "kappa": kappa,
                        "N": N,
                        "method": method,
                        "scale": scale,
                        "error": error,
                        "excess": excess,
                        "energy": energy,
                        "theory_energy": p["energy"],
                        "theory_noise": p["noise"]
                        if task == "additive"
                        else scale * scale * p["gamma"],
                        "theory_total": p["mse"]
                        if task == "additive"
                        else float(
                            np.sum(p["nominal"] ** 2) + scale * scale * p["gamma"]
                        ),
                    }
                )
            print(f"Measured {task}, kappa={kappa}, N={N}, trials={trials}", flush=True)
    arrays = {key: np.array([row[key] for row in records]) for key in records[0]}
    np.savez_compressed(RESULTS / f"raw_{task}.npz", **arrays)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "kind",
        nargs="?",
        choices=("all", "pred", "additive", "variation"),
        default="all",
    )
    parser.add_argument("--trials", type=int, default=2048)
    args = parser.parse_args()
    if args.trials < 2:
        parser.error("--trials must be at least two.")
    predictions()  # Written before any simulation starts.
    if args.kind == "pred":
        return
    for task in ("additive", "variation"):
        if args.kind in ("all", task):
            experiment(task, args.trials)
    from analyze import analyze
    from plots import build

    analyze()
    build()


if __name__ == "__main__":
    main()
