"""Compute paired-bootstrap ratio intervals from the saved trial arrays."""

import json
from pathlib import Path

import numpy as np
from common import NAME

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"


def paired(a, b, seed, bootstrap=500):
    ratio = float(a.mean() / b.mean())
    rng = np.random.default_rng(seed)
    values = []
    for _ in range(bootstrap):
        ids = rng.integers(0, len(a), len(a))
        values.append(a[ids].mean() / b[ids].mean())
    lo, hi = map(float, np.quantile(values, [0.025, 0.975]))
    return {"value": ratio, "lo": lo, "hi": hi}


def analyze():
    predictions = json.loads((RESULTS / "pred.json").read_text())
    summary = {"parameters": predictions["parameters"], "additive": [], "variation": []}
    text = [
        "# Experiment results",
        "",
        "Rows compare the same task, instance and N. Intervals are paired bootstrap intervals.",
        "Variation noise is deviation from the common Chebyshev terminal, not total error.",
        "Its prediction is first order; additive predictions are exact finite-noise MSE.",
        "",
    ]
    for task in ("additive", "variation"):
        path = RESULTS / f"raw_{task}.npz"
        if not path.exists():
            continue
        with np.load(path, allow_pickle=False) as data:
            index = {
                (int(k), int(n), str(m)): j
                for j, (k, n, m) in enumerate(
                    zip(data["kappa"], data["N"], data["method"])
                )
            }
            for j in range(len(data["N"])):
                k, N, m = (
                    int(data["kappa"][j]),
                    int(data["N"][j]),
                    str(data["method"][j]),
                )
                curve = predictions[task].get(str(k), {}).get(m, [])
                point = next((p for p in curve if p["N"] == N), None)
                if point is None or not np.isclose(
                    point["energy"], data["theory_energy"][j], rtol=1e-8, atol=0
                ):
                    raise ValueError(
                        f"{path.name} does not match pred.json; rerun {task}."
                    )
                ref = index[k, N, "pref"]
                key = "error" if task == "additive" else "excess"
                samples, base = data[key][j], data[key][ref]
                ci = (
                    {"value": 1.0, "lo": 1.0, "hi": 1.0}
                    if j == ref
                    else paired(samples, base, SEED + k + N)
                )
                ours = index[k, N, "flat" if task == "additive" else "balanced"]
                direct = (
                    {"value": 1.0, "lo": 1.0, "hi": 1.0}
                    if j == ours
                    else paired(data[key][ours], samples, SEED + k + N)
                )
                row = {
                    "kappa": k,
                    "N": N,
                    "method": m,
                    "trials": len(samples),
                    "ratio": ci,
                    "ours_over_method": direct,
                    "measured_mse": float(data["error"][j].mean()),
                    "measured_noise": float(data["excess"][j].mean()),
                    "energy_ratio": float(data["energy"][j] / data["energy"][ref]),
                    "energy_measured": float(data["energy"][j]),
                    "energy_predicted": float(data["theory_energy"][j]),
                    "noise_measured_over_predicted": float(
                        data["excess"][j].mean() / data["theory_noise"][j]
                    ),
                    "full_mse_ratio": float(
                        data["error"][j].mean() / data["error"][ref].mean()
                    ),
                    "predicted_ratio": float(
                        data["theory_total"][j] / data["theory_total"][ref]
                    )
                    if task == "additive"
                    else float(data["theory_noise"][j] / data["theory_noise"][ref]),
                }
                summary[task].append(row)
        text += [
            f"## {task}: largest horizon",
            "",
            "| κ | Method | Measured ratio to Prefix [95% interval] | Theory ratio | Our method / competitor [95% interval] |",
            "|---:|---|---:|---:|---:|",
        ]
        largest = max(r["N"] for r in summary[task])
        for r in summary[task]:
            if r["N"] != largest:
                continue
            q = r["ratio"]
            d = r["ours_over_method"]
            text.append(
                f"| {r['kappa']} | {NAME[r['method']]} | {q['value']:.4g} [{q['lo']:.4g}, {q['hi']:.4g}] | {r['predicted_ratio']:.4g} | {d['value']:.4g} [{d['lo']:.4g}, {d['hi']:.4g}] |"
            )
        text.append("")
        if task == "variation":
            text += [
                "For full-MSE ratios, including the common nominal bias, see summary.json.",
                "",
            ]
    (RESULTS / "summary.json").write_text(
        json.dumps(summary, indent=2, allow_nan=False) + "\n"
    )
    (RESULTS / "report.md").write_text("\n".join(text) + "\n")
    return predictions, summary


SEED = 17013
if __name__ == "__main__":
    analyze()
