"""Small literal operator-model FC/RFC mechanism experiment.

This is separate from fixed-objective benchmarks and their performance
profiles. It simulates the verified observed-probe protocol and evaluates
terminal virtual gradients only for the external mathematical error metric.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import tempfile
from pathlib import Path

import numpy as np

from xrbench.methods.fc_exact import operator_cycle


def _relative_norm(gradient, eigenvalues):
    return float(np.linalg.norm(gradient / np.sqrt(eigenvalues)))


def _scenario(dimension, seed, delta, kappa=100.0):
    """Fixed reference and norm-one symmetric increments in its energy metric."""
    rng = np.random.default_rng(seed)
    eigenvalues = np.geomspace(1.0, kappa, dimension)
    root = np.sqrt(eigenvalues)
    base = np.diag(eigenvalues)
    initial = rng.normal(size=dimension)
    increments = []
    for _ in range(dimension):
        H = rng.normal(size=(dimension, dimension))
        H = (H + H.T) / 2
        H /= np.linalg.norm(H, 2)
        increments.append((root[:, None] * H) * root[None, :])
    # Total historical variation is delta; the final correction budget is
    # also delta. Intermediate correction operators equal their search ones.
    operators, current = [], base.copy()
    for k in range(dimension):
        if k:
            current = current + (delta / (dimension - 1)) * increments[k - 1]
        operators.append(current.copy())
    corrections = [A.copy() for A in operators]
    corrections[-1] += delta * increments[-1]
    fingerprint = hashlib.sha256(
        initial.tobytes() + b"".join(A.tobytes() for A in operators + corrections)
    ).hexdigest()
    return eigenvalues, initial, operators, corrections, fingerprint


def run_mechanisms():
    records = []
    deltas = (1e-2, 3e-3, 1e-3, 3e-4, 1e-4, 3e-5, 1e-5)
    for n in (4, 8):
        for seed in range(3):
            for delta in deltas:
                eigen, initial, operators, corrections, fingerprint = _scenario(n, seed, delta)
                denominator = _relative_norm(initial, eigen)
                for method in ("FC", "RFC"):
                    record = dict(
                        method=method,
                        dimension=n,
                        seed=seed,
                        kappa=100.0,
                        delta=delta,
                        scenario_sha256=fingerprint,
                        information="observed directional operator probes",
                        fixed_objective=False,
                        initial_gradients=1,
                        search_probes=n,
                        final_correction_evaluated=False,
                    )
                    try:
                        rows = operator_cycle(
                            operators, corrections, initial, correction=method == "RFC"
                        )
                        terminal = rows[-1]["gradient"]
                        error = _relative_norm(terminal, eigen) / denominator
                        record.update(
                            success=bool(math.isfinite(error) and error > 0),
                            error=error,
                            error_over_delta=error / delta,
                            error_over_delta_squared=error / delta**2,
                            evaluated_corrections=sum(row["correction_evaluated"] for row in rows),
                            terminal_virtual=rows[-1]["final_virtual"],
                        )
                    except (np.linalg.LinAlgError, FloatingPointError) as exc:
                        record.update(success=False, error=None, reason=str(exc))
                    records.append(record)
    return records


def _sci(value):
    if value == 0:
        return "$0$"
    exponent = int(math.floor(math.log10(abs(value))))
    return f"${value / 10**exponent:.2f}\\times10^{{{exponent}}}$"


def generate(output_dir):
    """Write one vector figure, one native TeX table, and a small JSONL log."""
    cache = Path(tempfile.gettempdir()) / "xr-render-cache"
    cache.mkdir(parents=True, exist_ok=True)
    os.environ.setdefault("MPLCONFIGDIR", str(cache / "matplotlib"))
    os.environ.setdefault("XDG_CACHE_HOME", str(cache))
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    destination = Path(output_dir)
    for child in ("figures", "tables", "logs"):
        (destination / child).mkdir(parents=True, exist_ok=True)
    records = run_mechanisms()
    with (destination / "logs" / "theory.jsonl").open("w") as stream:
        for record in records:
            stream.write(json.dumps(record, sort_keys=True, allow_nan=False) + "\n")
    plt.rcParams.update(
        {
            "font.size": 9,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )
    figure, axes = plt.subplots(1, 2, figsize=(7.0, 2.65), constrained_layout=True)
    summaries = {}
    for ax, n in zip(axes, (4, 8)):
        for method, color, marker in (("FC", "#174A71", "o"), ("RFC", "#D16C18", "s")):
            rows = [row for row in records if row["dimension"] == n and row["method"] == method]
            grid = sorted({row["delta"] for row in rows})
            values = []
            low, high = [], []
            for delta in grid:
                cohort = [row["error"] for row in rows if row["delta"] == delta and row["success"]]
                summaries[n, method, delta] = (
                    float(np.median(cohort)) if cohort else math.nan,
                    len(cohort),
                )
                values.append(float(np.median(cohort)) if len(cohort) == 3 else math.nan)
                low.append(min(cohort) if len(cohort) == 3 else math.nan)
                high.append(max(cohort) if len(cohort) == 3 else math.nan)
            ax.loglog(
                grid,
                values,
                color=color,
                marker=marker,
                markersize=3.5,
                linewidth=1.6,
                label=method,
            )
            ax.fill_between(grid, low, high, color=color, alpha=0.10, linewidth=0)
            # A slope guide is labelled as such, rather than a fitted theorem.
            power = 1 if method == "FC" else 2
            index = 3
            guide = values[index] * (np.asarray(grid) / grid[index]) ** power
            ax.loglog(grid, guide, color=color, linestyle=":", linewidth=0.7, alpha=0.6)
        ax.set(
            title=f"{n} atoms, condition number 100",
            xlabel=r"Total variation $\delta$",
            ylabel=r"Relative terminal $A^{-1}$ gradient norm",
        )
        ax.grid(True, which="major", alpha=0.18, linewidth=0.5)
        ax.legend(frameon=False, loc="upper left")
    figure.savefig(
        destination / "figures" / "fc_rfc.pdf",
        metadata={"Title": "FC and RFC: operator-model variation response"},
    )
    plt.close(figure)
    lines = [
        r"\begin{table}[t]",
        r"\centering",
        r"\begin{tabular}{rrrrr}",
        r"\toprule",
        r"Atoms & $\delta$ & FC residual/$\delta$ & RFC residual/$\delta^2$ & Seeds\\",
        r"\midrule",
    ]
    for n in (4, 8):
        for delta in (1e-2, 1e-3, 1e-4, 1e-5):
            fc, count_fc = summaries[n, "FC", delta]
            rfc, count_rfc = summaries[n, "RFC", delta]
            cells = [
                str(n),
                _sci(delta),
                _sci(fc / delta) if math.isfinite(fc) else "--",
                _sci(rfc / delta**2) if math.isfinite(rfc) else "--",
                f"{min(count_fc, count_rfc)}/3",
            ]
            lines.append(" & ".join(cells) + r"\\")
        if n == 4:
            lines.append(r"\midrule")
    lines += [
        r"\bottomrule",
        r"\end{tabular}",
        r"\caption{Observed-probe operator model, median over three fixed seeds. Historical relative variation and the final correction budget both equal $\delta$. All intermediate RFC corrections are evaluated; the last correction is an unevaluated output whose true gradient is assessed only externally. These costs are separate from fixed-objective performance profiles.}",
        r"\label{tab:fc-rfc-mechanism}",
        r"\end{table}",
    ]
    (destination / "tables" / "mechanisms.tex").write_text("\n".join(lines) + "\n")
    return dict(
        runs=len(records),
        failures=sum(not row["success"] for row in records),
        figure="figures/fc_rfc.pdf",
        table="tables/mechanisms.tex",
        log="logs/theory.jsonl",
    )
