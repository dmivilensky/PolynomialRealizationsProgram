"""Two single-page vector PDFs: theoretical curves and measured markers."""

import json
import logging
from pathlib import Path

import matplotlib

matplotlib.use("pdf")
import matplotlib.pyplot as plt
import numpy as np
from common import ADDITIVE, NAME, VARIATION
from matplotlib.lines import Line2D
from matplotlib.ticker import FuncFormatter, MaxNLocator, NullFormatter, NullLocator

HERE = Path(__file__).resolve().parent
COLOR = {
    "flat": "#2377b4",
    "balanced": "#2377b4",
    "pref": "#666666",
    "lf": "#009e73",
    "dfb": "#8868b0",
    "masg": "#c48a00",
    "sine": "#d65b25",
}


def build():
    logging.getLogger("fontTools.ttLib.tables._h_e_a_d").setLevel(logging.ERROR)
    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.serif": ["DejaVu Serif"],
            "mathtext.fontset": "cm",
            "font.size": 8,
            "axes.labelsize": 8,
            "legend.fontsize": 7,
            "xtick.labelsize": 7,
            "ytick.labelsize": 7,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.linewidth": 0.6,
            "axes.grid": True,
            "grid.color": "#e6e5e0",
            "grid.linewidth": 0.5,
            "lines.linewidth": 1.3,
            "pdf.fonttype": 42,
        }
    )
    P = json.loads((HERE / "results/pred.json").read_text())
    S = json.loads((HERE / "results/summary.json").read_text())
    output = HERE / "figures"
    output.mkdir(exist_ok=True)
    for task, methods in [("additive", ADDITIVE), ("variation", VARIATION)]:
        if not S[task]:
            continue
        if task == "variation":
            fig, axes = plt.subplots(
                2,
                3,
                figsize=(6.5, 5.15),
                sharex="col",
                gridspec_kw={"width_ratios": (1, 1, 0.68)},
            )
            for row in range(2):
                axes[row, 1].sharey(axes[row, 0])
                axes[row, 1].tick_params(labelleft=False)
        else:
            fig, axes = plt.subplots(2, 2, figsize=(6.5, 5.15), sharex="col")
        handles = [
            Line2D(
                [],
                [],
                color=COLOR[m],
                ls=":" if m == "pref" else "-",
                marker="o",
                ms=3,
                markeredgecolor="white",
                markeredgewidth=0.4,
                label=NAME[m],
            )
            for m in methods
        ]
        fig.legend(
            handles=handles,
            loc="upper center",
            bbox_to_anchor=(0.5, 0.998),
            ncol=len(methods),
            frameon=False,
            handlelength=1.7,
            columnspacing=1.1,
        )
        for col, kappa in enumerate(P["parameters"]["kappas"][task]):
            curves = P[task][str(kappa)]
            reference = {r["N"]: r for r in curves["pref"]}
            for method in methods:
                if task == "variation" and method == "lf":
                    continue
                curve = curves[method]
                x = np.array([r["N"] / np.sqrt(kappa) for r in curve])
                for row in range(2):
                    field = (
                        "energy"
                        if (task == "additive" and row == 1)
                        or (task == "variation" and row == 0)
                        else "mse"
                        if task == "additive"
                        else "gamma"
                    )
                    y = [r[field] / reference[r["N"]][field] for r in curve]
                    axes[row, col].plot(
                        x,
                        y,
                        color=COLOR[method],
                        ls=":" if method == "pref" else "-",
                        lw=1.8 if method in ("flat", "balanced") else 1.2,
                    )
            for r in S[task]:
                if r["kappa"] != kappa:
                    continue
                if task == "variation" and r["method"] == "lf":
                    continue
                x = r["N"] / np.sqrt(kappa)
                m = r["method"]
                energy_row = 1 if task == "additive" else 0
                stat_row = 1 - energy_row
                axes[energy_row, col].plot(
                    x,
                    r["energy_ratio"],
                    "o",
                    ms=3.3,
                    color=COLOR[m],
                    mec="white",
                    mew=0.45,
                )
                q = r["ratio"]
                axes[stat_row, col].errorbar(
                    x,
                    q["value"],
                    yerr=[
                        [max(0, q["value"] - q["lo"])],
                        [max(0, q["hi"] - q["value"])],
                    ],
                    fmt="o",
                    ms=3.3,
                    color=COLOR[m],
                    mec="white",
                    mew=0.45,
                    elinewidth=0.7,
                    capsize=1.3,
                )
            for row, ax in enumerate(axes[:, col]):
                ax.set_xscale("log")
                ax.set_yscale("linear" if task == "variation" else "log")
                ax.axhline(1, color=COLOR["pref"], lw=0.7, ls=":")
                ticks = np.array([64, 128, 256, 512, 1024]) / np.sqrt(kappa)
                ax.set_xticks(ticks)
                ax.xaxis.set_major_formatter(FuncFormatter(lambda x, p: f"{x:.2g}"))
                ax.xaxis.set_minor_locator(NullLocator())
                ax.yaxis.set_minor_formatter(NullFormatter())
                if row == 0:
                    ax.set_title(rf"$\kappa={kappa:,}$")
                if row == 1:
                    ax.set_xlabel(r"Horizon $N/\sqrt{\kappa}$")
                ylabel = (
                    ("Terminal MSE / Prefix", "Energy gain / Prefix")
                    if task == "additive"
                    else ("Local energy gain / Prefix", "Noise variance / Prefix")
                )
                if task == "additive" or col == 0:
                    ax.set_ylabel(ylabel[row])
                if task == "variation":
                    ax.yaxis.set_major_locator(MaxNLocator(4))
        if task == "variation":
            # LF is retained in a separate scale. Its normalized predictions
            # are kappa-independent in this commuting family; show both MC sets.
            kappas = P["parameters"]["kappas"][task]
            base = P[task][str(kappas[0])]
            ref = {r["N"]: r for r in base["pref"]}
            for row, field in enumerate(("energy", "gamma")):
                ax = axes[row, 2]
                curve = base["lf"]
                x = [r["N"] for r in curve]
                y = [r[field] / ref[r["N"]][field] for r in curve]
                ax.plot(x, y, color=COLOR["lf"], lw=1.3)
                for ki, kappa in enumerate(kappas):
                    for r in S[task]:
                        if r["method"] != "lf" or r["kappa"] != kappa:
                            continue
                        marker = "o" if ki == 0 else "s"
                        face = COLOR["lf"] if ki == 0 else "white"
                        if row == 0:
                            ax.plot(
                                r["N"],
                                r["energy_ratio"],
                                marker=marker,
                                ms=3.3,
                                color=COLOR["lf"],
                                mfc=face,
                                mec=COLOR["lf"],
                                mew=0.6,
                            )
                        else:
                            q = r["ratio"]
                            ax.errorbar(
                                r["N"],
                                q["value"],
                                yerr=[
                                    [max(0, q["value"] - q["lo"])],
                                    [max(0, q["hi"] - q["value"])],
                                ],
                                fmt=marker,
                                ms=3.3,
                                color=COLOR["lf"],
                                mfc=face,
                                mec=COLOR["lf"],
                                mew=0.6,
                                elinewidth=0.7,
                                capsize=1.3,
                            )
                ax.set(xscale="log", yscale="log")
                ax.set_xticks([64, 256, 1024])
                ax.xaxis.set_major_formatter(FuncFormatter(lambda x, p: f"{x:g}"))
                ax.xaxis.set_minor_locator(NullLocator())
                ax.yaxis.set_minor_formatter(NullFormatter())
                ax.set_yticks([4, 8, 16] if row == 0 else [32, 128, 512])
                ax.yaxis.set_major_formatter(FuncFormatter(lambda x, p: f"{x:g}"))
                ax.yaxis.tick_right()
                if row == 0:
                    ax.set_title("LF/fractal")
                else:
                    ax.set_xlabel(r"Horizon $N$")
        fig.tight_layout(rect=(0, 0, 1, 0.925))
        fig.savefig(output / f"{task}.pdf", bbox_inches="tight", pad_inches=0.03)
        plt.close(fig)
    print("Figures:", output)


if __name__ == "__main__":
    build()
