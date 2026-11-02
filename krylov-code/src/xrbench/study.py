"""Compact, reproducible figures and native TeX tables from completed runs.

The input is the small JSONL history written by the campaign runner.  A result
row represents one method on one problem instance; repeated timing trials must
be aggregated by the runner, rather than silently counted as different problems.
This module never launches solvers or evaluates an objective retrospectively.

Performance profiles follow Dolan and More, Math. Program. 91 (2002), 201--213,
https://arxiv.org/abs/cs/0102001.  Failures (including missing scheduled runs)
have infinite performance ratio.  All-failed problems stay in the denominator.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import tempfile
from collections import Counter
from collections.abc import Mapping, Sequence
from importlib.metadata import version
from pathlib import Path
from statistics import median
from typing import Any

PRIMARY_METHODS = (
    "XR",
    "XR-F",
    "L-BFGS",
    "L-CG_DESCENT",
    "MS-L-BFGS",
    "SC-MSS",
    "L-SR1",
    "O-ACCEL",
)
CUTEST_GROUPS = ("sos-small", "sos-large", "general-small", "general-large")
GROUP_LABELS = {
    "sos-small": r"Sums of squares, $n\leq300$",
    "sos-large": r"Sums of squares, $n>300$",
    "general-small": r"General objectives, $n\leq300$",
    "general-large": r"General objectives, $n>300$",
    "quadratic": "Quadratic objectives",
}
SUITE_LABELS = {
    "quadratic": "Quadratic",
    "perturbed": "Smoothly perturbed",
    "local": "Full-memory local test",
    "cutest": "CUTEst",
    "ablation": "Ablation",
    "libsvm": "Regularized logistic regression",
}
STYLE = {
    "XR": ("#0072B2", "-", "o"),
    "XR-F": ("#D62728", "-", "s"),
    "L-BFGS": ("#008744", (0, (5, 2)), "^"),
    "L-CG_DESCENT": ("#242424", "-", "D"),
    "MS-L-BFGS": ("#7B35B2", (0, (5, 2)), "v"),
    "SC-MSS": ("#008B8B", "-", "P"),
    "L-SR1": ("#C02B86", (0, (5, 2)), "x"),
    "O-ACCEL": ("#BE5500", (0, (5, 2)), "+"),
}


def _index(records: Sequence[Mapping[str, Any]]) -> dict[tuple[str, str, str], Mapping]:
    result = {}
    for row in records:
        key = tuple(str(row[k]) for k in ("suite", "problem", "method"))
        if key in result:
            raise ValueError(f"Duplicate result {key}; aggregate timing repetitions first")
        result[key] = row
    return result


def _validate_aliases(records: Sequence[Mapping]) -> None:
    by_job = {row["job_id"]: row for row in records if row.get("job_id")}
    for row in records:
        if not row.get("alias_of"):
            continue
        source = by_job.get(row["alias_of"])
        if source is None or source.get("alias_of"):
            raise ValueError("An ablation alias must name a present, originally computed run")
        for field in (
            "status",
            "success",
            "n_g",
            "n_f",
            "n_fg",
            "n_pts",
            "seconds",
            "cpu_seconds",
            "setup_seconds",
            "milestones",
            "trace",
            "info",
        ):
            if row.get(field) != source.get(field):
                raise ValueError(f"Alias {row.get('job_id')} changed observed field {field}")


def _successful(row: Mapping | None) -> bool:
    return row is not None and row.get("success") is True


def _cost(row: Mapping | None, metric: str) -> float:
    if not _successful(row):
        return math.inf
    try:
        value = float(row[metric])
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError(f"Successful row has no valid {metric}: {row}") from exc
    if not math.isfinite(value) or value <= 0:
        raise ValueError(f"Successful cost must be positive and finite: {metric}={value}")
    return value


def performance_profiles(
    records: Sequence[Mapping[str, Any]],
    methods: Sequence[str],
    problems: Sequence[str],
    metric: str = "n_g",
    *,
    suite: str = "cutest",
) -> dict[str, Any]:
    """Return exact empirical profiles on an explicitly supplied common cohort.

    ``problems`` includes scheduled instances even when no solver completed.
    Missing results are reported separately; they do not disappear from a plot.
    Ties all receive ratio one.  No arbitrary finite penalty is used for failure.
    """
    if len(set(methods)) != len(methods) or len(set(problems)) != len(problems):
        raise ValueError("The method and problem lists must contain unique identifiers")
    index = _index(records)
    ratios: dict[str, list[float]] = {method: [] for method in methods}
    missing = []
    all_failed = []
    for problem in problems:
        values = {}
        for method in methods:
            row = index.get((suite, problem, method))
            if row is None:
                missing.append((problem, method))
            values[method] = _cost(row, metric)
        best = min(values.values(), default=math.inf)
        if not math.isfinite(best):
            all_failed.append(problem)
        for method, value in values.items():
            ratios[method].append(value / best if math.isfinite(value) else math.inf)
    grid = sorted({1.0} | {r for values in ratios.values() for r in values if math.isfinite(r)})
    n = len(problems)
    curves = {
        method: [sum(r <= x for r in values) / n if n else 0.0 for x in grid]
        for method, values in ratios.items()
    }
    return {
        "methods": list(methods),
        "problems": list(problems),
        "metric": metric,
        "ratios": ratios,
        "x": grid,
        "curves": curves,
        "missing": missing,
        "all_failed": all_failed,
        "n": n,
    }


def profile_view_ranges(profile: Mapping) -> dict[str, Any]:
    """Both panels show every finite ratio, independently of which method wins."""
    finite = [
        ratio for values in profile["ratios"].values() for ratio in values if math.isfinite(ratio)
    ]
    full = 2 ** max(4, math.ceil(math.log2(max(finite, default=1))))
    conditional_n = profile["n"] - len(profile["all_failed"])
    limit = math.log(2 * conditional_n + 1) if conditional_n else 1.0
    return {
        "full_xlim": (1.0, float(full)),
        "full_ylim": (0.0, 1.02),
        "logit_xlim": (1.0, float(full)),
        "logit_ylim": (-limit * 1.04, limit * 1.04),
    }


def conditional_logit_profile(profile: Mapping) -> dict[str, Any]:
    """Empirical logits conditional on at least one recorded success.

    A failed individual method retains its infinite ratio. Only problems on
    which every compared method failed are excluded, explicitly and uniformly.
    The half-count correction is a display transform, never a replacement cost.
    """
    keep = [
        i
        for i in range(profile["n"])
        if any(math.isfinite(values[i]) for values in profile["ratios"].values())
    ]
    n = len(keep)
    counts = {
        method: [sum(values[i] <= x for i in keep) for x in profile["x"]]
        for method, values in profile["ratios"].items()
    }
    return {
        "n": n,
        "excluded": profile["n"] - n,
        "counts": counts,
        "curves": {
            method: [math.log((k + 0.5) / (n - k + 0.5)) if n else math.nan for k in values]
            for method, values in counts.items()
        },
    }


def conditional_logit_ticks(n: int) -> tuple[list[float], list[str]]:
    """Label empirical-logit coordinates by their original conditional percentages.

    Endpoints and 50% are always shown. Add 90%, then 99%, only if each
    additional label is at least 14% of the complete vertical span from all
    existing labels. This avoids crowding near 100% on small cohorts.
    """
    if not n:
        return [], []

    def coordinate(probability):
        return math.log((n * probability + 0.5) / (n * (1 - probability) + 0.5))

    probabilities = [0.0, 0.5, 1.0]
    gap = 0.28 * math.log(2 * n + 1)
    for candidate in (0.9, 0.99):
        if all(abs(coordinate(candidate) - coordinate(p)) >= gap for p in probabilities):
            probabilities.append(candidate)
    probabilities.sort()
    return [coordinate(p) for p in probabilities], [f"{100 * p:g}%" for p in probabilities]


def _ordered(methods: Sequence[str]) -> list[str]:
    return [m for m in PRIMARY_METHODS if m in methods] + sorted(
        set(methods) - set(PRIMARY_METHODS)
    )


def _geomean(values: Sequence[float]) -> float | None:
    if not values:
        return None
    return 0.0 if 0 in values else math.exp(sum(math.log(x) for x in values) / len(values))


def _tex(value: Any) -> str:
    escapes = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(escapes.get(c, c) for c in str(value))


def _number(value: float | None, digits: int = 2) -> str:
    if value is None or not math.isfinite(value):
        return "--"
    if value == 0:
        return "0"
    if abs(value) >= 10000 or abs(value) < 0.01:
        return f"{value:.{digits}g}"
    return f"{value:.{digits}f}".rstrip("0").rstrip(".")


def _math_number(value: float, digits: int = 2) -> str:
    """Format a scalar inside TeX math, including scientific notation."""
    formatted = _number(value, digits)
    if "e" not in formatted:
        return formatted
    mantissa, exponent = formatted.split("e")
    power = f"10^{{{int(exponent)}}}"
    return power if mantissa == "1" else mantissa + r"\times " + power


def _table(
    path: Path,
    columns: str,
    header: Sequence[str],
    rows: Sequence[Sequence],
    caption: str,
    label: str,
) -> None:
    columns, header, rows, caption = _publication_table(columns, header, rows, caption, label)
    # Repeated denominators and fixed settings belong in the caption rather
    # than an entire constant column. Their exact values, including failures,
    # remain explicit; no observation is removed from the underlying table.
    protected = {"Method", "Variant", "Setting", "Group", "Stratum", "Suite"}
    common = [
        i
        for i, name in enumerate(header)
        if name not in protected and len(rows) > 1 and len({str(row[i]) for row in rows}) == 1
    ]
    if common:
        caption += (
            " Common to all rows: " + "; ".join(f"{header[i]} = {rows[0][i]}" for i in common) + "."
        )
        keep = [i for i in range(len(header)) if i not in common]
        if keep:
            columns = "".join(columns[i] for i in keep)
            header = [header[i] for i in keep]
            rows = [[row[i] for i in keep] for row in rows]
    lines = [
        "% Generated from the current campaign; do not edit by hand.",
        r"\begin{table}[tbp]",
        r"\centering",
        r"\small",
        f"\\begin{{tabular}}{{{columns}}}",
        r"\hline",
        " & ".join(header) + r" \\",
        r"\hline",
    ]
    lines.extend(" & ".join(str(x) for x in row) + r" \\" for row in rows)
    lines += [
        r"\hline",
        r"\end{tabular}",
        f"\\caption{{{caption}}}",
        f"\\label{{{label}}}",
        r"\end{table}",
        "",
    ]
    path.write_text("\n".join(lines), encoding="utf-8")


def _publication_table(columns, header, rows, caption, label):
    """Presentation only: frozen study scripts retain their original SHA pins."""
    header, rows = list(header), [list(row) for row in rows]
    if label == "tab:xr-settings":
        j = header.index("$+/-$")
        header[j : j + 1] = ["Variant only", "Base only"]
        columns = columns[:j] + "rr" + columns[j + 1 :]
        for row in rows:
            row[j : j + 1] = row[j].split("/")
        j = header.index("Neither")
        header.pop(j)
        columns = columns[:j] + columns[j + 1 :]
        for row in rows:
            row.pop(j)
        header[header.index(r"$N_g/N_g^{\rm base}$")] = (
            r"$N_g^{\mathrm{variant}}/N_g^{\mathrm{base}}$"
        )
        caption = (
            r"Fixed-parameter sensitivity on 16 CUTEst instances. Ratios are geometric means of "
            r"$N_g^{\mathrm{variant}}/N_g^{\mathrm{base}}$ on instances solved by both settings. "
            r"Base settings are marked in each method family. Variant only and Base only count "
            r"exclusive successes. XR and XR-F use memory cap 100 and vary $m_0$; MS-L-BFGS "
            r"stores eight pairs and varies its simultaneous-secant limit."
        )
    if label == "tab:bfgs-reference":
        j = header.index("XR only / other only")
        header[j : j + 1] = ["XR only", "Method only"]
        columns = columns[:j] + "rr" + columns[j + 1 :]
        for row in rows:
            row[j : j + 1] = row[j].split("/")
        header[header.index(r"$N_g/N_g^{\rm XR}$")] = r"$N_g^{\mathrm{method}}/N_g^{\mathrm{XR}}$"
        caption = (
            r"Full-memory BFGS-SP reference on CUTEst instances with $n\le300$ and twelve quadratics, "
            r"at relative gradient tolerance $10^{-8}$. Gradient ratios are geometric means "
            r"on instances solved by both methods. Paired counts and ratios pool the 149 CUTEst "
            r"instances and twelve controls (161 problems). XR only and Method only count exclusive successes."
        )
    if label == "tab:tighter-target":
        header[header.index(r"$N_g^{10}/N_g^8$")] = r"$N_g(10^{-10})/N_g(10^{-8})$"
        caption = (
            r"Gradient-tolerance sensitivity on 16 CUTEst instances, four per objective/dimension "
            r"group, selected by the fixed hash rule. Ratios are geometric means on instances "
            r"solved at both tolerances. Every run uses the same preset, 100000-point budget "
            r"and 120-second limit."
        )
    if label == "tab:xr-ablations":
        header[header.index("Cost/base")] = r"$N_g^{\mathrm{variant}}/N_g^{\mathrm{base}}$"
        caption = (
            r"One-factor variants of the baseline in the first row. Ratios are geometric means "
            r"on instances solved by both variants; values above one favor the baseline. "
            r"Base only and Variant only count exclusive successes."
        )
    if label in {f"tab:xr-{suite}" for suite in SUITE_LABELS}:
        suite = label.removeprefix("tab:xr-")
        caption = (
            f"{_tex(SUITE_LABELS[suite])} results. Wins count the smallest gradient cost, including ties. "
            r"$N_g$, $N_f$ and seconds are geometric means over each method's successful instances. "
            r"$N_g$ and $N_f$ count actual gradient and function evaluations."
        )
    if label == "tab:xr-perturbations":
        header[header.index("L-BFGS/XR-F")] = r"$N_g^{\mathrm{L\!BFGS}}/N_g^{\mathrm{XR\!F}}$"
        caption = (
            r"Full perturbation grid. Each ratio is "
            r"$\exp\{\operatorname{median}\log(N_g^{\mathrm{L\!BFGS}}/N_g^{\mathrm{XR\!F}})\}$ "
            r"over seeds solved by both methods. Values above one favor XR-F. "
            r"XR-F only and L-BFGS only count exclusive successes."
        )
    if label == "tab:xr-diagnostics":
        header = [
            {
                "$w$": "Window",
                "$m$": "Capacity",
                "Rank/1k$g$": "Rank drops",
                "Drop/1k$g$": "Window drops",
                "F pass/fail": "F pass/fallback",
            }.get(h, h)
            for h in header
        ]
        caption = (
            "Primary-XR model diagnostics over all completed runs. Window is the median per-run "
            "mean retained-pair count; Capacity is the median largest memory capacity. "
            "Rank and window deletions are totals per 1000 gradient evaluations. "
            "F pass/fallback counts corrected-model gate decisions."
        )
    header = ["Both solved" if h in {"Paired", "Pairs"} else h for h in header]
    return columns, header, rows, caption


def _compact_markdown_tables(lines: Sequence[str]) -> list[str]:
    """Move repeated administrative counts to an explicit shared statement.

    Cohort/method labels and cost statistics remain columns. Exact common
    counts, including nonzero failures, remain printed after their table.
    """
    eligible = {
        "Missing",
        "Solved",
        "Solved/16",
        "Paired",
        "Both solved",
        "Jointly solved",
        "Attained",
        "Ours only",
        "Variant only",
        "Base only",
        "Method only",
        "XR only",
        "Competitor only",
        "Neither",
        "Completed",
        "Diagnosed/run",
        "Quadratics solved",
        "Solved 1e-8",
        "Solved 1e-10",
        "XR-only / method-only",
        "Variant-only / base-only",
        "Median lower bound",
        "Median upper bound",
        "Max upper bound",
        "Median max cap",
    }
    compact, i = [], 0
    while i < len(lines):
        if not lines[i].startswith("|"):
            compact.append(lines[i])
            i += 1
            continue
        end = i
        while end < len(lines) and lines[end].startswith("|"):
            end += 1
        block = [
            [part.strip() for part in line.strip().strip("|").split("|")] for line in lines[i:end]
        ]
        if len(block) < 4 or any(len(row) != len(block[0]) for row in block):
            compact.extend(lines[i:end])
            i = end
            continue
        header, alignment, *rows = block
        if not all(set(cell) <= {"-", ":", " "} and "-" in cell for cell in alignment):
            compact.extend(lines[i:end])
            i = end
            continue
        if "Setting" in header and "Neither" in header:
            j = header.index("Variant-only / base-only")
            header[j : j + 1] = ["Variant only", "Base only"]
            alignment[j : j + 1] = ["---:", "---:"]
            for row in rows:
                row[j : j + 1] = row[j].split("/")
            j = header.index("Neither")
            header.pop(j)
            alignment.pop(j)
            for row in rows:
                row.pop(j)
        for original, replacement in (
            ("Paired gradient ratio to XR", "Gradient ratio (method/XR)"),
            ("Paired gradient increase", "Gradient ratio (tight/base)"),
        ):
            if original in header:
                j = header.index(original)
                header[j : j + 1] = [replacement, "Both solved"]
                alignment[j : j + 1] = ["---:", "---:"]
                for row in rows:
                    ratio, _, count = row[j].partition(" (")
                    row[j : j + 1] = [ratio, count.removesuffix(" pairs)")]
        if "XR-only / method-only" in header:
            j = header.index("XR-only / method-only")
            header[j : j + 1] = ["XR only", "Method only"]
            alignment[j : j + 1] = ["---:", "---:"]
            for row in rows:
                row[j : j + 1] = row[j].split("/")
        header = [
            {
                "Paired": "Both solved",
                "Jointly solved": "Both solved",
                "Gradient ratio to own base": "Gradient ratio (variant/base)",
            }.get(h, h)
            for h in header
        ]
        if "Ratio" in header and "Our method" in header:
            header[header.index("Ratio")] = "Gradient ratio (competitor/ours)"
        block = [header, alignment, *rows]
        common = [
            j
            for j, name in enumerate(header)
            if name in eligible and len({row[j] for row in rows}) == 1
        ]
        keep = [j for j in range(len(header)) if j not in common]
        if common and keep:
            compact += ["| " + " | ".join(row[j] for j in keep) + " |" for row in block]
            compact += [
                "",
                "Common across this table: "
                + "; ".join(f"{header[j]} = {rows[0][j]}" for j in common)
                + ".",
            ]
        else:
            compact += ["| " + " | ".join(row) + " |" for row in block]
        i = end
    return compact


def _cohort(records: Sequence[Mapping], expected_problems: Sequence[Mapping] | None) -> list[dict]:
    metadata = {}
    if expected_problems is not None:
        allowed = {(str(p["suite"]), str(p["problem"])) for p in expected_problems}
        unexpected = {(str(r["suite"]), str(r["problem"])) for r in records} - allowed
        if unexpected:
            raise ValueError(f"Results outside the frozen problem cohort: {sorted(unexpected)}")
    for problem in [*(expected_problems or []), *records]:
        key = (str(problem["suite"]), str(problem["problem"]))
        candidate = {
            k: problem.get(k)
            for k in (
                "suite",
                "problem",
                "group",
                "n",
                "problem_spec",
                "dataset",
                "samples",
                "regularization",
                "storage",
            )
        }
        if candidate["problem_spec"] is None and (
            "source" in problem or ("kappa" in problem and "epsilon" in problem)
        ):
            candidate["problem_spec"] = dict(problem)
        if key in metadata:
            for field in (
                "group",
                "n",
                "problem_spec",
                "dataset",
                "samples",
                "regularization",
                "storage",
            ):
                old, new = metadata[key].get(field), candidate.get(field)
                if (
                    field == "problem_spec"
                    and isinstance(old, Mapping)
                    and isinstance(new, Mapping)
                ):
                    # Analysis-only development tags can be added to the frozen
                    # cohort without pretending to change the observed objective.
                    shared = set(old) & set(new) - {"development_role"}
                    if any(old[name] != new[name] for name in shared):
                        raise ValueError(f"Inconsistent problem metadata for {key}: {field}")
                    continue
                if old is not None and new is not None and old != new:
                    raise ValueError(f"Inconsistent problem metadata for {key}: {field}")
                if old is None:
                    metadata[key][field] = new
        else:
            metadata[key] = candidate
    return [metadata[key] for key in sorted(metadata)]


def _methods_by_suite(
    records: Sequence[Mapping], expected: Sequence[str] | Mapping | None, cohort: Sequence[Mapping]
) -> dict[str, list[str]]:
    methods = {}
    for suite in sorted({p["suite"] for p in cohort}):
        observed = {r["method"] for r in records if r["suite"] == suite}
        requested = expected.get(suite) if isinstance(expected, Mapping) else expected
        if requested is not None:
            unexpected = observed - set(requested)
            if unexpected:
                raise ValueError(f"Unexpected methods in {suite}: {sorted(unexpected)}")
            methods[suite] = list(requested)
        else:
            methods[suite] = _ordered(list(observed))
    return methods


def _summary_rows(
    records: Sequence[Mapping], cohort: Sequence[Mapping], methods: Mapping, labels: Mapping
) -> list[dict]:
    index = _index(records)
    summaries = []
    for suite, names in methods.items():
        problems = [p["problem"] for p in cohort if p["suite"] == suite]
        profile = performance_profiles(records, names, problems, suite=suite)
        for method in names:
            rows = [index.get((suite, problem, method)) for problem in problems]
            success = [row for row in rows if _successful(row)]
            summaries.append(
                {
                    "suite": suite,
                    "method": method,
                    "label": labels.get(method, method),
                    "n": len(problems),
                    "success": len(success),
                    "missing": sum(row is None for row in rows),
                    "wins": sum(value == 1 for value in profile["ratios"][method]),
                    "n_g": _geomean([_cost(row, "n_g") for row in success]),
                    "n_f": _geomean([float(row.get("n_f", 0)) for row in success]),
                    "seconds": _geomean([_cost(row, "seconds") for row in success]),
                }
            )
    return summaries


def _paired(
    records: Sequence[Mapping],
    problems: Sequence[str],
    ours: str,
    other: str,
    metric: str = "n_g",
    suite: str = "cutest",
) -> dict:
    index = _index(records)
    ratios, ours_only, other_only, neither = [], 0, 0, 0
    for problem in problems:
        a, b = (index.get((suite, problem, method)) for method in (ours, other))
        if _successful(a) and _successful(b):
            ratios.append(_cost(b, metric) / _cost(a, metric))
        elif _successful(a):
            ours_only += 1
        elif _successful(b):
            other_only += 1
        else:
            neither += 1
    return {
        "ours": ours,
        "other": other,
        "paired": len(ratios),
        "ratio": _geomean(ratios),
        "ours_only": ours_only,
        "other_only": other_only,
        "neither": neither,
    }


def _perturbed_grid(
    records: Sequence[Mapping], cohort: Sequence[Mapping] | None = None
) -> dict | None:
    """All prespecified perturbation instances against one fixed competitor.

    A cell uses the median log ratio on jointly successful seeds and retains
    both exclusive-success counts. It never substitutes a capped failure cost.
    """
    rows = [r for r in records if r["suite"] == "perturbed"]
    instances = {}
    for row in [*rows, *(p for p in (cohort or []) if p["suite"] == "perturbed")]:
        spec = row.get("problem_spec") or {}
        if "kappa" not in spec or "epsilon" not in spec:
            return None
        instances[row["problem"]] = (float(spec["kappa"]), float(spec["epsilon"]))
    if not instances or not {"XR-F", "L-BFGS"} <= {r["method"] for r in rows}:
        return None
    index = _index(rows)
    kappas = sorted({value[0] for value in instances.values()})
    epsilons = sorted({value[1] for value in instances.values()})
    cells = {}
    for kappa in kappas:
        for epsilon in epsilons:
            problems = [p for p, value in instances.items() if value == (kappa, epsilon)]
            ratios, ours_only, other_only = [], 0, 0
            for problem in problems:
                ours = index.get(("perturbed", problem, "XR-F"))
                other = index.get(("perturbed", problem, "L-BFGS"))
                if _successful(ours) and _successful(other):
                    ratios.append(math.log2(_cost(other, "n_g") / _cost(ours, "n_g")))
                elif _successful(ours):
                    ours_only += 1
                elif _successful(other):
                    other_only += 1
            cells[kappa, epsilon] = {
                "logratio": median(ratios) if ratios else None,
                "paired": len(ratios),
                "n": len(problems),
                "ours_only": ours_only,
                "other_only": other_only,
            }
    return {"kappas": kappas, "epsilons": epsilons, "cells": cells}


def _shared_full_pair_count(cells: Mapping) -> str | None:
    """Suppress repeated cell counts only for one common, completely solved cohort."""
    values = list(cells.values())
    sizes = {cell["n"] for cell in values}
    if len(sizes) != 1 or next(iter(sizes)) <= 0:
        return None
    if any(
        cell["paired"] != cell["n"] or cell["ours_only"] or cell["other_only"] for cell in values
    ):
        return None
    n = next(iter(sizes))
    return f"{n}/{n}"


def _family_sensitivity(
    records: Sequence[Mapping], cohort: Sequence[Mapping], methods: Sequence[str]
) -> list[dict]:
    """Reweight each panel by explicit CUTEst family, without dropping failures.

    Each family has total weight one, irrespective of its number of dimensions
    or SIF parameterizations. No family is guessed from a display name.
    """
    output = []
    for group in CUTEST_GROUPS:
        problems = [p for p in cohort if p["suite"] == "cutest" and p.get("group") == group]
        if not problems:
            continue
        families = {p["problem"]: (p.get("problem_spec") or {}).get("source") for p in problems}
        if any(not source for source in families.values()):
            return []
        counts = Counter(families.values())
        ids = [p["problem"] for p in problems]
        profile = performance_profiles(records, methods, ids)
        weight = [1 / counts[families[problem]] for problem in ids]
        total = len(counts)
        for method in methods:
            ratios = profile["ratios"][method]
            output.append(
                {
                    "group": group,
                    "method": method,
                    "n": len(ids),
                    "families": total,
                    "raw_win": sum(ratio == 1 for ratio in ratios) / len(ids),
                    "family_win": sum(w for w, ratio in zip(weight, ratios) if ratio == 1) / total,
                    "family_solved": sum(
                        w for w, ratio in zip(weight, ratios) if math.isfinite(ratio)
                    )
                    / total,
                }
            )
    return output


def _development_sensitivity(
    records: Sequence[Mapping], cohort: Sequence[Mapping], methods: Sequence[str]
) -> list[dict]:
    """Prespecified development strata; remaining cases are not called held out."""
    output = []
    for role in ("development", "pilot-diagnostic", "remaining-benchmark"):
        problems = [
            p
            for p in cohort
            if p["suite"] == "cutest"
            and (p.get("problem_spec") or {}).get("development_role") == role
        ]
        if not problems:
            continue
        families = {p["problem"]: p["problem_spec"].get("source") for p in problems}
        if any(not source for source in families.values()):
            return []
        counts = Counter(families.values())
        ids = [p["problem"] for p in problems]
        profile = performance_profiles(records, methods, ids)
        weights = [1 / counts[families[problem]] for problem in ids]
        for method in methods:
            ratios = profile["ratios"][method]
            output.append(
                {
                    "role": role,
                    "method": method,
                    "n": len(ids),
                    "families": len(counts),
                    "family_solved": sum(w for w, r in zip(weights, ratios) if math.isfinite(r))
                    / len(counts),
                    "family_win": sum(w for w, r in zip(weights, ratios) if r == 1) / len(counts),
                }
            )
    return output


def _diagnostics(records: Sequence[Mapping]) -> list[dict]:
    """Observed primary-XR diagnostics, including stopped and capped runs."""
    output = []
    for group in (*CUTEST_GROUPS, "quadratic"):
        for method in ("XR", "XR-F"):
            rows = [
                r
                for r in records
                if r["suite"] == "cutest" and r.get("group") == group and r["method"] == method
            ]
            if not rows:
                continue
            reasons, counters = Counter(), Counter()
            windows, caps, lower, upper = [], [], [], []
            diagnosed = 0
            for row in rows:
                info = row.get("info") or {}
                reason = str(row.get("status", "unspecified"))
                if not _successful(row) and info.get("stop"):
                    reason += ": " + str(info["stop"])
                reasons[reason] += 1
                observed = info.get("counters") or {}
                diagnosed += bool(observed)
                counters.update(
                    {
                        k: v
                        for k, v in observed.items()
                        if isinstance(v, (int, float)) and math.isfinite(v)
                    }
                )
                value = info.get("mean_window")
                if isinstance(value, (int, float)) and math.isfinite(value):
                    windows.append(value)
                value = (info.get("growing_memory") or {}).get("maximum")
                if isinstance(value, (int, float)) and math.isfinite(value):
                    caps.append(value)
                bounds = info.get("spectral_estimates")
                if (
                    bounds
                    and len(bounds) == 2
                    and all(isinstance(v, (int, float)) and math.isfinite(v) for v in bounds)
                ):
                    lower.append(bounds[0])
                    upper.append(bounds[1])
            gradients = sum(r.get("n_g", 0) for r in rows)
            output.append(
                {
                    "group": group,
                    "method": method,
                    "completed": len(rows),
                    "solved": sum(_successful(r) for r in rows),
                    "diagnosed": diagnosed,
                    "reasons": dict(reasons),
                    "counters": dict(counters),
                    "window": median(windows) if windows else None,
                    "capacity": median(caps) if caps else None,
                    "rank_per_1000g": 1000 * counters.get("nrank_deleted", 0) / gradients
                    if gradients
                    else None,
                    "window_per_1000g": 1000 * counters.get("nwindow_deleted", 0) / gradients
                    if gradients
                    else None,
                    "lower": median(lower) if lower else None,
                    "upper": median(upper) if upper else None,
                    "upper_max": max(upper) if upper else None,
                }
            )
    return output


def _context_counts(cohort: Sequence[Mapping]) -> tuple[int, int]:
    """Count objective/start pairs separately from ablation display contexts."""
    identities = set()
    for problem in cohort:
        spec = problem.get("problem_spec") or problem
        if problem["suite"] in ("cutest", "ablation") and spec.get("source"):
            identity = (
                "cutest",
                spec["source"],
                problem.get("n"),
                json.dumps(spec.get("sif"), sort_keys=True),
                json.dumps(spec.get("start", "CUTEst default"), sort_keys=True),
            )
        else:
            identity = (problem["suite"], problem["problem"])
        identities.add(identity)
    return len(cohort), len(identities)


def _prepare_plot_cache() -> None:
    cache = Path(tempfile.gettempdir()) / "xr-render-cache"
    cache.mkdir(exist_ok=True)
    os.environ.setdefault("MPLCONFIGDIR", str(cache / "matplotlib"))
    os.environ.setdefault("XDG_CACHE_HOME", str(cache))


def _timing_description(manifest: Mapping) -> list[str]:
    workers = manifest.get("workers", "unspecified")
    threads = (manifest.get("environment") or {}).get("blas_threads", "unspecified")
    mode = (
        "Solver runs were measured sequentially, one process at a time."
        if workers == 1
        else f"The campaign used {workers} concurrent solver processes; wall times measure that workload."
    )
    return [
        f"{mode} Each process used {threads} BLAS thread(s). "
        "Each method–problem pair contributes one timed run; no timing-repeat "
        "aggregation is applied.",
        "",
    ]


def _implementation_description(manifest: Mapping) -> list[str]:
    implementations = manifest.get("implementations") or {}
    if implementations:
        return [
            "Implementation provenance:",
            "",
            "| Method | Timed implementation |",
            "|---|---|",
            *[f"| {method} | {description} |" for method, description in implementations.items()],
            "",
            "Wall time includes the measured solver control, model operations and oracle calls. "
            "Shared Python oracle callbacks and numerical libraries are included consistently.",
            "",
        ]
    competitors = (
        "MS-L-BFGS, SC-MSS, SC-SR1 and O-ACCEL use our C implementations of the published "
        "algorithms, checked against their sources; these are source-faithful ports, not "
        "author-distributed C executables."
        if manifest.get("competitor_native_backend")
        else "MS-L-BFGS, SC-MSS, SC-SR1 and O-ACCEL use Python control with NumPy/SciPy kernels."
    )
    xr = (
        "XR/XR-F use C control/model kernels with Python oracle callbacks. "
        if manifest.get("native_backend")
        else "XR uses Python control with NumPy/SciPy kernels. "
    )
    return [
        "Wall time includes solver control and linear-algebra overhead. CG_DESCENT uses "
        "author C through its adapter; L-BFGS uses SciPy's compiled L-BFGS-B optimizer. "
        + xr
        + competitors,
        "",
    ]


def _native_provenance(manifest: Mapping, output: Path) -> list[str]:
    """Describe the frozen executable and a distinct, measured port pilot."""
    lines = []
    hardware = manifest.get("hardware") or {}
    if hardware:
        lines += [
            f"Hardware: {hardware.get('processor', 'unspecified')}, "
            f"{hardware.get('cpu_cores', 'unspecified')} CPU cores "
            f"({hardware.get('performance_cores', 'unspecified')} performance / "
            f"{hardware.get('efficiency_cores', 'unspecified')} efficiency), "
            f"{hardware.get('memory_gb', 'unspecified')} GB memory. "
            f"Hardware metadata source: `{hardware.get('source', 'unspecified')}`.",
            "",
        ]
    backend = manifest.get("native_backend") or {}
    if backend:
        lines += [
            "XR/XR-F use the frozen C executor and model kernels, with the unchanged "
            "common Python oracle. SciPy supplies compiled BLAS/LAPACK and QR-update "
            "routines; the independent Python XR implementation is the reference, "
            "not the timed executor.",
            "",
            f"Native compiler: `{backend.get('compiler_version', 'unspecified')}`. "
            f"Flags: `{' '.join(backend.get('flags', []))}`. "
            f"Python ABI: `{backend.get('python_abi', 'unspecified')}`; "
            f"numerical ABI: `{backend.get('blas_abi', 'unspecified')}`.",
            "",
            f"Native build key: `{backend.get('build_key', 'unspecified')}`; "
            f"extension SHA-256: `{backend.get('extension_sha256', 'unspecified')}`. "
            "The manifest records individual C/header SHA-256 fingerprints. These "
            "identify the executable; they do not certify floating-point execution.",
            "",
        ]
    competitor_backend = manifest.get("competitor_native_backend") or {}
    if competitor_backend:
        lines += [
            "The four additional competitors execute their complete control loops and model "
            "updates in our C ports of the published methods, through the same oracle and "
            "SciPy BLAS/LAPACK capsule ABI as XR. Author-code availability and the detailed "
            "equation/source comparisons are documented in the method audits.",
            "",
            f"Competitor native build key: `{competitor_backend.get('build_key', 'unspecified')}`; "
            f"extension SHA-256: `{competitor_backend.get('extension_sha256', 'unspecified')}`. "
            f"Compiler: `{competitor_backend.get('compiler_version', 'unspecified')}`; "
            f"flags: `{' '.join(competitor_backend.get('flags', []))}`.",
            "",
        ]
    pilot = manifest.get("native_port_pilot") or {}
    if pilot:
        lines += ["Native-port pilot policy: " + str(pilot.get("policy", "see manifest")), ""]
        path = Path(__file__).resolve().parents[2] / pilot.get("report", "")
        if path.is_file():
            audit = json.loads(path.read_text())
            cases = audit.get("cases", [])
            speedups = [
                c["speedup"]
                for c in cases
                if isinstance(c.get("speedup"), (int, float)) and math.isfinite(c["speedup"])
            ]
            scope = (
                "same scientific fingerprint as this campaign"
                if audit.get("source_hash") == manifest.get("source_hash")
                else "a historical scientific fingerprint, different from this campaign"
            )
            lines += [
                f"Pilot: [native-port-pilot.json]({os.path.relpath(path, output)}), "
                f"SHA-256 `{hashlib.sha256(path.read_bytes()).hexdigest()}`; producer "
                f"`{audit.get('source_hash', 'unspecified')}` ({scope}). "
                f"Protocol: {audit.get('protocol', 'unspecified')}.",
                "",
            ]
            if speedups:
                lines += [
                    f"Across {len(cases)} paired diagnostic cases, median Python/native "
                    f"elapsed-time ratios range from {_number(min(speedups))} to "
                    f"{_number(max(speedups))}. Nonlinear floating-point trajectories "
                    "and oracle counts can change; no bitwise-equivalence claim is "
                    "made. These end-to-end ratios include any resulting change in "
                    "work, not just per-iteration overhead. The serial pilot is "
                    "separate from the concurrent benchmark: no pilot time rescales "
                    "a campaign observation, and every own-method and synthetic "
                    "benchmark observation is measured anew.",
                    "",
                ]
    return lines + _native_campaign_provenance(manifest, output)


def _native_campaign_provenance(
    manifest: Mapping, output: Path, comparison_path: Path | None = None
) -> list[str]:
    """Use the paired port comparison only when it pins these exact final inputs."""
    path = comparison_path or (
        Path(__file__).resolve().parents[2] / "artifacts/logs/native-campaign-comparison.json"
    )
    manifest_path, history_path = output / "manifest.json", output / "history.jsonl"
    if not path.is_file() or not manifest_path.is_file() or not history_path.is_file():
        return []
    comparison = json.loads(path.read_text())
    native = comparison.get("native") or {}
    if (
        native.get("source_hash") != manifest.get("source_hash")
        or native.get("manifest_sha256") != hashlib.sha256(manifest_path.read_bytes()).hexdigest()
        or native.get("history_sha256") != hashlib.sha256(history_path.read_bytes()).hexdigest()
    ):
        return []
    rows = comparison.get("methods") or {}
    if not rows:
        return []
    lines = [
        "**Paired full-cohort implementation comparison.** "
        f"[native-campaign-comparison.json]({os.path.relpath(path, output)}), "
        f"SHA-256 `{hashlib.sha256(path.read_bytes()).hexdigest()}`, matches the "
        "current scientific source and the exact current manifest/history checksums. "
        + str(comparison.get("scope", "See linked comparison for the fixed cohort.")),
        "",
        "| Method | Joint successes | Python/native wall ratio | Python/native Ng ratio | Native only | Python only |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for method in ("XR", "XR-F"):
        if method not in rows:
            continue
        values = rows[method]
        lines.append(
            f"| {method} | {values['jointly_successful']}/{values['total']} | "
            f"{_number(values['python_over_native_wall_geomean'])} | "
            f"{_number(values['python_over_native_gradients_geomean'], digits=3)} | "
            f"{len(values['native_only'])} | {len(values['python_only'])} |"
        )
    lines += [
        "",
        "Ratios are geometric means on each method's jointly successful cases. "
        "The gradient ratio measures actual work-count changes, not a rescaling "
        "of time. Nonlinear trajectories, oracle counts and solved sets differ; "
        "no bitwise or identical-outcomes claim is made. These are single-run "
        "observations from separate concurrent phases with matched presets, "
        "targets, budgets, environment and worker load, rather than isolated "
        "serial per-iteration timings. Exclusive successes remain explicit; "
        "detailed counts, statuses and both input fingerprints are in the linked "
        "JSON. No timing correction or substitution is applied to the primary profiles.",
        "",
    ]
    return lines


def _qualitative_findings(records, cohort, methods, *, complete):
    """Interpret actual paired results without substituting a success narrative."""
    if not complete:
        return [
            "The campaign is incomplete. Completion order favors short runs, so "
            "qualitative conclusions about comparative efficiency and reliability "
            "are deferred until every scheduled observation is available."
        ]
    paragraphs = []
    names = methods.get("cutest", [])
    problems = [p["problem"] for p in cohort if p["suite"] == "cutest"]
    if "XR-F" in names and "L-CG_DESCENT" in names:
        gradients = _paired(records, problems, "XR-F", "L-CG_DESCENT")
        timing = performance_profiles(records, names, problems, "seconds")
        cg_early = timing["curves"]["L-CG_DESCENT"][0]
        our_early = max(timing["curves"].get(m, [0])[0] for m in ("XR", "XR-F"))
        efficiency = (
            "XR-F and native CG_DESCENT have no jointly solved cases, so no paired cost is inferred"
            if gradients["ratio"] is None
            else "XR-F uses fewer gradients than native CG_DESCENT on their jointly solved cases"
            if gradients["ratio"] is not None and gradients["ratio"] > 1
            else "native CG_DESCENT uses fewer gradients than XR-F on their jointly solved cases"
            if gradients["ratio"] is not None and gradients["ratio"] < 1
            else "XR-F and native CG_DESCENT have equal paired geometric mean gradient costs"
        )
        early = (
            "Native CG_DESCENT has the larger share of outright time wins than either "
            "XR variant; its early lead is visible before the later XR plateau. "
            if cg_early > our_early
            else "The time profile's first-ratio winners and its eventual plateaux "
            "measure different properties. "
        )
        paragraphs.append(
            "**Efficiency versus reliability.** "
            + efficiency
            + ". "
            + early
            + "High eventual coverage does not imply uniform speed: the full time "
            "range exposes both implementation overhead and the tail of difficult "
            "cases. The ordinary profile retains every failed instance; its "
            "conditional logit companion resolves near-saturation differences "
            "without turning all-method failures into successes."
        )
    if all(m in names for m in ("XR", "XR-F")):
        fcost = _paired(records, problems, "XR-F", "XR")
        fvalues = _paired(records, problems, "XR-F", "XR", metric="n_f")
        direction = (
            "has no jointly solved cases for assessing"
            if fcost["ratio"] is None
            else "reduces"
            if fcost["ratio"] is not None and fcost["ratio"] > 1
            else "increases"
            if fcost["ratio"] is not None and fcost["ratio"] < 1
            else "leaves unchanged"
        )
        values = (
            "provides no paired function-cost estimate"
            if fvalues["ratio"] is None
            else "also lowers the paired function-evaluation cost"
            if fvalues["ratio"] is not None and fvalues["ratio"] > 1
            else "does not lower the paired function-evaluation cost"
        )
        coverage = (
            "F solves additional instances but also loses others"
            if fcost["ours_only"] and fcost["other_only"]
            else "F adds solved instances without losing any of XR's successes"
            if fcost["ours_only"]
            else "F loses some of XR's successes without adding new ones"
            if fcost["other_only"]
            else "the two variants solve exactly the same instances"
        )
        paragraphs.append(
            f"**What F buys.** On jointly solved CUTEst cases, the endpoint-value "
            f"correction {direction} the geometric mean gradient cost and {values}; "
            f"{coverage}. This is a tradeoff between richer curvature information, "
            "extra value work and gate decisions, rather than an unconditional "
            "acceleration. The diagnostic counters retain correction passes, "
            "fallbacks and safeguard events so that these costs remain visible."
        )
    ablations = methods.get("ablation", [])
    if "XR-F" in ablations and "XR-F/fixed-memory" in ablations:
        ids = [p["problem"] for p in cohort if p["suite"] == "ablation"]
        memory = _paired(records, ids, "XR-F", "XR-F/fixed-memory", suite="ablation")
        effect = (
            "There are no jointly solved cases for a paired memory-cost comparison"
            if memory["ratio"] is None
            else "Growing memory lowers paired gradient costs relative to the fixed window"
            if memory["ratio"] is not None and memory["ratio"] > 1
            else "Growing memory does not lower paired gradient costs relative to the fixed window"
        )
        paragraphs.append(
            "**Memory and safeguards.** " + effect + "; exclusive successes are "
            "reported alongside that paired comparison. A larger permitted memory "
            "is not the same as a larger retained independent window: rank filtering, "
            "window deletion and safeguards remain active. The ablations isolate "
            "these mechanisms one at a time; they do not establish that a single "
            "setting dominates on every objective family."
        )
    grid = _perturbed_grid(records, cohort)
    if grid:
        cells = list(grid["cells"].values())
        measured = [cell for cell in cells if cell["logratio"] is not None]
        positive = sum(cell["logratio"] > 0 for cell in measured)
        description = (
            "no perturbation cell has a jointly solved seed, so no finite paired "
            "cost comparison is inferred"
            if not measured
            else "XR-F's paired gradient advantage over L-BFGS persists across every "
            "evaluated condition-number/perturbation cell"
            if positive == len(cells) and cells
            else "XR-F's paired gradient advantage over L-BFGS occurs in some, "
            "rather than all, condition-number/perturbation cells"
            if positive
            else "the full perturbation grid does not show a paired gradient "
            "advantage for XR-F over L-BFGS"
        )
        paragraphs.append(
            "**Controlled structure and scope.** " + description + ". The whole "
            "grid, all seeds and exclusive failures remain visible; the quadratic "
            "trajectory is a fixed illustration rather than a selected best case. "
            "These controlled gains do not transfer automatically to arbitrary "
            "nonlinear CUTEst problems. Accepted-iterate local accuracy is examined "
            "separately and is not an empirical proof of the conditional R-order theorem."
        )
    return paragraphs


def _plots(
    records: Sequence[Mapping],
    cohort: Sequence[Mapping],
    methods: Mapping,
    labels: Mapping,
    output: Path,
    missing_count: int,
) -> list[Path]:
    # Matplotlib is optional until the artifact command is actually requested.
    _prepare_plot_cache()
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.ticker import FuncFormatter

    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 8,
            "axes.titlesize": 9,
            "axes.labelsize": 8,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.linewidth": 0.5,
            "grid.color": "#E2E5E8",
            "grid.linewidth": 0.5,
            "pdf.fonttype": 42,
            "savefig.facecolor": "white",
            "legend.fontsize": 8,
            "xtick.labelsize": 7.5,
            "ytick.labelsize": 7.5,
        }
    )
    artifacts = []

    def style(method, i):
        color, dash, marker = STYLE.get(method, (f"C{i % 10}", "--", "o"))
        return dict(
            color=color,
            linestyle=dash,
            marker=marker,
            linewidth=1.8 if method in ("XR", "XR-F") else 1.0,
            markersize=3,
            markerfacecolor="white",
            markeredgewidth=0.7,
        )

    def legend(fig, names):
        if not names:
            return
        handles = [Line2D([], [], **style(method, i)) for i, method in enumerate(names)]
        fig.legend(
            handles,
            [labels.get(m, m) for m in names],
            loc="lower center",
            ncol=min(4, len(names)),
            frameon=False,
            columnspacing=1.5,
            handlelength=3,
            bbox_to_anchor=(0.5, 0.005),
        )

    def save(fig, name):
        path = output / "figures" / name
        fig.savefig(
            path,
            metadata={"Creator": "XR reproducible study", "CreationDate": None, "ModDate": None},
        )
        plt.close(fig)
        artifacts.append(path)

    if "cutest" in methods:
        names = methods["cutest"]
        for metric, filename, axis_label in (
            ("n_g", "cutest_gradients.pdf", "Gradient-evaluation ratio"),
            ("seconds", "cutest_time.pdf", "Wall-time ratio"),
        ):
            fig = plt.figure(figsize=(7.1, 6.7))
            cards = fig.add_gridspec(
                2,
                2,
                left=0.09,
                right=0.965,
                top=0.94 if missing_count else 0.97,
                bottom=0.13,
                hspace=0.43,
                wspace=0.18,
            )
            drawing_order = [m for m in names if m not in ("XR", "XR-F")] + [
                m for m in ("XR", "XR-F") if m in names
            ]
            for j, group in enumerate(CUTEST_GROUPS):
                inner = cards[j // 2, j % 2].subgridspec(2, 1, height_ratios=[1.15, 1], hspace=0.32)
                ax, logit_ax = fig.add_subplot(inner[0]), fig.add_subplot(inner[1])
                problems = [
                    p["problem"]
                    for p in cohort
                    if p["suite"] == "cutest" and p.get("group") == group
                ]
                profile = performance_profiles(records, names, problems, metric)
                conditional = conditional_logit_profile(profile)
                views = profile_view_ranges(profile)
                xmax = views["full_xlim"][1]
                if not problems:
                    ax.text(
                        0.5,
                        0.5,
                        "No scheduled instances",
                        ha="center",
                        va="center",
                        transform=ax.transAxes,
                        color="#777777",
                    )
                for axis, view in ((ax, "full"), (logit_ax, "logit")):
                    xright = views[view + "_xlim"][1]
                    for method in drawing_order:
                        i = names.index(method)
                        options = style(method, i)
                        marker = options.pop("marker")
                        values = (
                            profile["curves"][method]
                            if view == "full"
                            else conditional["curves"][method]
                        )
                        axis.step(
                            [*profile["x"], xmax],
                            [*values, values[-1]],
                            where="post",
                            **options,
                        )
                        # Place markers evenly in log ratio, at genuine ECDF
                        # values. Different phases separate exact coincidences
                        # without shifting curves or changing probabilities.
                        phase = (i + 0.5) / max(1, len(names))
                        markers_x = [2 ** ((k + phase) * math.log2(xright) / 4) for k in range(4)]
                        ratios = profile["ratios"][method]
                        markers_y = [
                            sum(r <= x for r in ratios) / profile["n"] if profile["n"] else 0
                            for x in markers_x
                        ]
                        if view == "logit":
                            n = conditional["n"]
                            markers_y = [
                                math.log((k + 0.5) / (n - k + 0.5)) if n else math.nan
                                for k in (sum(r <= x for r in ratios) for x in markers_x)
                            ]
                        axis.plot(
                            markers_x,
                            markers_y,
                            linestyle="none",
                            marker=marker,
                            color=options["color"],
                            markersize=2.7,
                            markerfacecolor="white",
                            markeredgewidth=0.65,
                        )
                    axis.set_xscale("log", base=2)
                    axis.set_xlim(*views[view + "_xlim"])
                    axis.set_ylim(*views[view + "_ylim"])
                    exponent = int(math.log2(xright))
                    stride = max(1, math.ceil(exponent / 5))
                    axis.set_xticks([2**k for k in range(0, exponent + 1, stride)])
                    axis.xaxis.set_major_formatter(FuncFormatter(lambda x, pos: f"{x:g}"))
                    if view == "full":
                        axis.set_yticks([0, 0.5, 1])
                    else:
                        ticks, tick_labels = conditional_logit_ticks(conditional["n"])
                        axis.set_yticks(ticks, tick_labels)
                        axis.axhline(0, color="#A9AFB4", linewidth=0.5)
                    axis.grid(True, alpha=0.8)
                    axis.set_axisbelow(True)
                    if j % 2 == 0:
                        axis.set_ylabel("Fraction" if view == "full" else "Conditional solved")
                ax.set_title(f"{GROUP_LABELS[group]}  ({len(problems)})", loc="left")
                logit_ax.set_title(
                    f"Conditional on ≥1 success · N={conditional['n']}",
                    loc="left",
                    fontsize=7.2,
                    color="#626B71",
                    pad=2,
                )
                logit_ax.set_xlabel(axis_label)
                if not conditional["n"]:
                    logit_ax.text(
                        0.5,
                        0.5,
                        "No recorded success: conditional profile undefined",
                        ha="center",
                        va="center",
                        transform=logit_ax.transAxes,
                        fontsize=6.7,
                    )
                if profile["all_failed"]:
                    failure_label = (
                        "No recorded success" if profile["missing"] else "All methods failed"
                    )
                    ax.text(
                        0.97,
                        0.06,
                        f"Full range · {failure_label.lower()}: {len(profile['all_failed'])}",
                        transform=ax.transAxes,
                        ha="right",
                        color="#666666",
                        fontsize=6.8,
                    )
            legend(fig, names)
            if missing_count:
                fig.text(
                    0.99,
                    0.995,
                    "INCOMPLETE CAMPAIGN",
                    ha="right",
                    va="top",
                    color="#A94444",
                    fontsize=7,
                )
            save(fig, filename)

    suites = [suite for suite in ("quadratic", "perturbed") if suite in methods]
    if suites:
        fig, axes = plt.subplots(1, len(suites), figsize=(7.1, 2.9), squeeze=False)
        plotted_methods = set()
        for suite, ax in zip(suites, axes.flat):
            perturbations = _perturbed_grid(records, cohort) if suite == "perturbed" else None
            if perturbations:
                import numpy as np

                kappas, epsilons = perturbations["kappas"], perturbations["epsilons"]
                cells = perturbations["cells"]
                matrix = np.array(
                    [
                        [cells[kappa, epsilon]["logratio"] for epsilon in epsilons]
                        for kappa in kappas
                    ],
                    dtype=float,
                )
                limit = max(
                    1.0, max((abs(v) for v in matrix.flat if math.isfinite(v)), default=1.0)
                )
                color_map = plt.get_cmap("RdBu").with_extremes(bad="#F0F2F4")
                heatmap = ax.imshow(
                    np.ma.masked_invalid(matrix),
                    cmap=color_map,
                    aspect="auto",
                    vmin=-limit,
                    vmax=limit,
                )
                ax.set_xticks(range(len(epsilons)), [f"{epsilon:g}" for epsilon in epsilons])
                ax.set_yticks(range(len(kappas)), [f"{kappa:g}" for kappa in kappas])
                ax.set_xticks([i - 0.5 for i in range(len(epsilons) + 1)], minor=True)
                ax.set_yticks([i - 0.5 for i in range(len(kappas) + 1)], minor=True)
                ax.tick_params(which="minor", length=0)
                ax.grid(which="minor", color="white", linewidth=0.8)
                ax.set_xlabel(r"Perturbation $\epsilon$")
                ax.set_ylabel(r"Condition number $\kappa$")
                shared_pairs = _shared_full_pair_count(cells)
                ax.set_title(
                    f"XR-F vs L-BFGS · all cells {shared_pairs} paired"
                    if shared_pairs
                    else "XR-F vs L-BFGS: all seeds",
                    loc="left",
                )
                for i, kappa in enumerate(kappas):
                    for j, epsilon in enumerate(epsilons):
                        cell = cells[kappa, epsilon]
                        logratio = cell["logratio"]
                        cost = f"{2**logratio:.2g}×" if logratio is not None else "--"
                        text = cost if shared_pairs else f"{cost}\n{cell['paired']}/{cell['n']}"
                        if cell["ours_only"] or cell["other_only"]:
                            text += f"\n+{cell['ours_only']} / −{cell['other_only']}"
                        color = (
                            "white"
                            if logratio is not None and abs(logratio) > limit * 0.6
                            else "#222222"
                        )
                        ax.text(
                            j,
                            i,
                            text,
                            ha="center",
                            va="center",
                            fontsize=7.4 if shared_pairs else 5.7,
                            color=color,
                        )
                colorbar = fig.colorbar(
                    heatmap, ax=ax, location="bottom", pad=0.28, fraction=0.05, aspect=30
                )
                colorbar.set_label(
                    r"$\log_2(N_g^{\mathrm{L\!BFGS}}/N_g^{\mathrm{XR\!F}})$",
                    fontsize=6.5,
                    labelpad=1,
                )
                colorbar.ax.tick_params(labelsize=6)
                continue
            candidates = sorted(p["problem"] for p in cohort if p["suite"] == suite)
            representative = candidates[0]
            # The same fixed five-method subset is used on every controlled panel.
            # Full solver results are retained in the generated summary table.
            names = [
                m
                for m in methods[suite]
                if m in ("XR", "XR-F", "L-BFGS", "L-CG_DESCENT", "MS-L-BFGS")
            ]
            if not names:
                names = methods[suite]
            selected = {
                method: next(
                    (
                        r
                        for r in records
                        if r["suite"] == suite
                        and r["problem"] == representative
                        and r["method"] == method
                    ),
                    None,
                )
                for method in names
            }
            traces = [row.get("trace", []) for row in selected.values() if row]
            field = (
                "error"
                if traces
                and all(
                    trace and all(t.get("error") is not None for t in trace) for trace in traces
                )
                else "gnorm"
            )
            for i, method in enumerate(names):
                row = selected[method]
                trace = row.get("trace", []) if row else []
                # Synthetic x*=0 gives an exact error when supplied by the runner.
                # Otherwise the figure explicitly uses relative gradient norm.
                points = []
                for event in trace:
                    x, y = event.get("n_g"), event.get(field)
                    if x is not None and y is not None and math.isfinite(float(y)) and y >= 0:
                        points.append((float(x), float(y)))
                scale = next((y for _, y in points if y > 0), None)
                if scale is None:
                    continue
                x, y = zip(*points)
                positive = [value / scale for value in y if value > 0]
                floor = min(positive, default=1e-16) * 0.2
                ax.plot(
                    x,
                    [max(value / scale, floor) for value in y],
                    markevery=(i % max(1, len(x)), max(1, len(x) // 5)),
                    **style(method, i),
                )
                plotted_methods.add(method)
            ax.set_yscale("log")
            ax.set_title(SUITE_LABELS[suite], loc="left")
            ax.set_xlabel("Gradient evaluations")
            ax.set_ylabel(
                "Best observed relative error"
                if field == "error"
                else "Best observed relative gradient norm"
            )
            ax.grid(True, alpha=0.8)
            ax.text(
                0.97,
                0.97,
                representative,
                ha="right",
                va="top",
                fontsize=6,
                transform=ax.transAxes,
                color="#666666",
            )
            if not ax.lines:
                ax.text(
                    0.5,
                    0.5,
                    "No trajectory recorded",
                    ha="center",
                    va="center",
                    transform=ax.transAxes,
                )
        legend(fig, _ordered(list(plotted_methods)))
        fig.subplots_adjust(
            left=0.075, right=0.985, top=0.88 if missing_count else 0.93, bottom=0.27, wspace=0.47
        )
        if missing_count:
            fig.text(
                0.99,
                0.995,
                "INCOMPLETE CAMPAIGN",
                ha="right",
                va="top",
                color="#A94444",
                fontsize=7,
            )
        save(fig, "controlled.pdf")
    if methods.get("libsvm"):
        artifacts.append(
            _plot_libsvm(records, cohort, methods["libsvm"], labels, output, missing_count)
        )
    return artifacts


def _libsvm_outcomes(records, problems, names):
    """Count observed minima on the complete scheduled per-penalty cohorts.

    Failed and missing observations have infinite cost. In particular, an
    all-failed problem never gives the XR family a spurious infinite tie.
    Missing competitors make recorded minima provisional, rather than changing
    the denominator or supplying an artificial finite observation.
    """
    index = _index(records)
    groups = {}
    for problem in problems:
        reg = float(
            (problem.get("problem_spec") or {}).get("regularization", problem.get("regularization"))
        )
        groups.setdefault(reg, []).append(problem["problem"])
    ours = [name for name in ("XR", "XR-F") if name in names]
    outcomes = []
    for reg, ids in sorted(groups.items(), reverse=True):
        selected = [index.get(("libsvm", problem, method)) for problem in ids for method in names]
        wins = {}
        for metric in ("n_g", "seconds"):
            count = 0
            for problem in ids:
                costs = {
                    method: _cost(index.get(("libsvm", problem, method)), metric)
                    for method in names
                }
                best = min(costs.values(), default=math.inf)
                count += math.isfinite(best) and any(costs[method] == best for method in ours)
            wins[metric] = count
        outcomes.append(
            dict(
                regularization=reg,
                datasets=len(ids),
                scheduled_runs=len(selected),
                converged_runs=sum(_successful(row) for row in selected),
                missing_runs=sum(row is None for row in selected),
                all_methods_solved=sum(
                    bool(names)
                    and all(_successful(index.get(("libsvm", problem, method))) for method in names)
                    for problem in ids
                ),
                xr_gradient_minima=wins["n_g"],
                xr_time_minima=wins["seconds"],
            )
        )
    return outcomes


def _libsvm_tables(records, cohort, names, labels, output):
    """Dataset descriptions and per-regularization paired costs; never evaluate f."""
    result = {"artifacts": [], "report": [], "comparisons": [], "outcomes": []}
    problems = [p for p in cohort if p["suite"] == "libsvm"]
    if not problems:
        return result
    catalog_path = Path(__file__).resolve().parent / "problems/libsvm.json"
    catalog = json.loads(catalog_path.read_text()) if catalog_path.exists() else {}
    catalog = {p["name"]: p for p in catalog.get("datasets", [])}
    datasets = {}
    for problem in problems:
        spec = {
            **(problem.get("problem_spec") or {}),
            **{k: v for k, v in problem.items() if v is not None},
        }
        dataset = spec.get("dataset")
        if not dataset:
            raise ValueError(f"LIBSVM context lacks its frozen dataset name: {problem['problem']}")
        if spec.get("regularization") is None:
            raise ValueError(f"LIBSVM context lacks regularization: {problem['problem']}")
        meta = catalog.get(dataset, {})
        entry = dict(
            dataset=dataset,
            samples=spec.get("samples", meta.get("rows")),
            features=(spec["n"] - 1) if spec.get("n") else meta.get("features"),
            storage=spec.get("storage", meta.get("storage", "unspecified")),
            group=spec.get("group", meta.get("group", "unspecified")),
        )
        if dataset in datasets and datasets[dataset] != entry:
            raise ValueError(f"Inconsistent frozen LIBSVM dataset metadata: {dataset}")
        datasets[dataset] = entry
    group_labels = {
        "moderate": "Moderate dimension",
        "many-samples": "Many observations",
        "dense-highdim": "Dense, high dimension",
        "sparse-highdim": "Sparse, high dimension",
    }
    dataset_rows = [
        [
            _tex(v["dataset"]),
            _tex(group_labels.get(v["group"], v["group"])),
            f"{v['samples']:,}" if v["samples"] is not None else "--",
            f"{v['features']:,}" if v["features"] is not None else "--",
            _tex(v["storage"]),
        ]
        for v in sorted(
            datasets.values(),
            key=lambda x: (
                list(group_labels).index(x["group"])
                if x["group"] in group_labels
                else len(group_labels),
                x["features"] or 0,
                x["dataset"],
            ),
        )
    ]
    path = output / "tables/libsvm_datasets.tex"
    _table(
        path,
        "llrrl",
        ["Dataset", "Structure", "Observations", "Features", "Storage"],
        dataset_rows,
        "Binary classification datasets for regularized logistic regression. "
        "Features exclude the appended intercept. Every nonzero feature row has unit "
        "Euclidean norm; all coefficients, including the intercept, are regularized. "
        "Each dataset uses the same frozen regularization grid and the zero initial point.",
        "tab:xr-libsvm-datasets",
    )
    result["artifacts"].append(path)
    regs = sorted(
        {
            float((p.get("problem_spec") or {}).get("regularization", p.get("regularization")))
            for p in problems
        },
        reverse=True,
    )
    reg_counts = Counter(
        float((p.get("problem_spec") or {}).get("regularization", p.get("regularization")))
        for p in problems
    )
    scheduled = (
        f"Each regularization level contains {next(iter(reg_counts.values()))} scheduled datasets. "
        if len(set(reg_counts.values())) == 1
        else "Scheduled dataset counts by regularization: "
        + "; ".join(f"{reg:g}: {reg_counts[reg]}" for reg in regs)
        + ". "
    )
    if "XR" in names:
        rows = []
        for reg in regs:
            ids = [
                p["problem"]
                for p in problems
                if float(
                    (p.get("problem_spec") or {}).get("regularization", p.get("regularization"))
                )
                == reg
            ]
            for method in names:
                if method == "XR":
                    continue
                gradients = _paired(records, ids, "XR", method, suite="libsvm")
                timing = _paired(records, ids, "XR", method, "seconds", suite="libsvm")
                result["comparisons"].append(
                    dict(regularization=reg, n=len(ids), **gradients, time_ratio=timing["ratio"])
                )
                rows.append(
                    [
                        (
                            f"$10^{{{round(math.log10(reg))}}}$"
                            if math.isclose(reg, 10 ** round(math.log10(reg)), rel_tol=1e-12)
                            else f"${reg:g}$"
                        ),
                        _tex(labels.get(method, method)),
                        _number(gradients["ratio"]),
                        _number(timing["ratio"]),
                        str(gradients["paired"]),
                        str(gradients["ours_only"]),
                        str(gradients["other_only"]),
                    ]
                )
        path = output / "tables/libsvm_comparisons.tex"
        header = [
            r"$\lambda$", "Method", "$N_g$/XR", "Time/XR",
            "Both solved", "XR only", "Method only",
        ]
        caption = (
            "Paired comparison against XR by regularization strength. Costs are geometric "
            "mean method/XR ratios on jointly solved datasets; values above one favor XR. "
        )
        all_solved = bool(rows) and all(
            comparison["paired"] == comparison["n"]
            for comparison in result["comparisons"]
        )
        if all_solved:
            header = header[:4]
            rows = [row[:4] for row in rows]
            caption += (
                f"All methods reach the target on all {next(iter(reg_counts.values()))} "
                "datasets at each regularization level."
                if len(set(reg_counts.values())) == 1
                else scheduled + "All methods reach the target on every scheduled dataset."
            )
        else:
            caption += scheduled + (
                "Both solved counts joint successes; XR only and Method only count "
                "successes exclusive to the corresponding method."
            )
        _table(
            path,
            "rlrr" if all_solved else "rlrrrrr",
            header,
            rows,
            caption,
            "tab:xr-libsvm-comparisons",
        )
        result["artifacts"].append(path)
    result["report"] = [
        "",
        "## Regularized logistic regression",
        "",
        f"The frozen LIBSVM cohort contains {len(datasets)} datasets and "
        f"{len(problems)} objective/start pairs at regularization strengths "
        + ", ".join(f"`{reg:g}`" for reg in regs)
        + ". "
        "The common zero start and preprocessing are fixed independently of results. "
        "The gradient and time profiles retain every scheduled objective; "
        "paired costs by regularization are generated in `tables/libsvm_comparisons.tex`.",
        "",
    ]
    result["outcomes"] = _libsvm_outcomes(records, problems, names)
    for item in result["outcomes"]:
        n = item["datasets"]
        paragraph = (
            f"At regularization `{item['regularization']:g}`, "
            f"{item['converged_runs']}/{item['scheduled_runs']} scheduled runs converged; "
            f"all compared methods solved {item['all_methods_solved']}/{n} datasets. "
        )
        if item["missing_runs"]:
            paragraph += (
                f"There are {item['missing_runs']} missing scheduled observations; "
                "recorded-minimum counts are provisional. "
            )
        if any(method in names for method in ("XR", "XR-F")):
            paragraph += (
                "XR or XR-F attained the minimum observed gradient count on "
                f"{item['xr_gradient_minima']}/{n} datasets and the minimum observed "
                f"wall time on {item['xr_time_minima']}/{n} datasets, counting ties. "
                "These counts describe observed minima; the two variants retain separate profiles."
            )
        result["report"] += [paragraph, ""]
    return result


def _plot_libsvm(records, cohort, names, labels, output, missing_count):
    """One compact gradient/time profile, each with ordinary and conditional scales."""
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.ticker import FuncFormatter

    ids = [p["problem"] for p in cohort if p["suite"] == "libsvm"]
    fig, axes = plt.subplots(2, 2, figsize=(7.1, 4.4), squeeze=False)
    drawing_order = [m for m in names if m not in ("XR", "XR-F")] + [
        m for m in ("XR", "XR-F") if m in names
    ]
    for col, (metric, title) in enumerate(
        (("n_g", "Gradient evaluations"), ("seconds", "Wall time"))
    ):
        profile = performance_profiles(records, names, ids, metric, suite="libsvm")
        conditional = conditional_logit_profile(profile)
        views = profile_view_ranges(profile)
        for row, kind in enumerate(("full", "logit")):
            ax = axes[row, col]
            right = views[kind + "_xlim"][1]
            for method in drawing_order:
                i = names.index(method)
                color, dash, marker = STYLE.get(method, (f"C{i % 10}", "--", "o"))
                values = (
                    profile["curves"][method] if kind == "full" else conditional["curves"][method]
                )
                ax.step(
                    [*profile["x"], right],
                    [*values, values[-1]],
                    where="post",
                    color=color,
                    linestyle=dash,
                    linewidth=1.8 if method in ("XR", "XR-F") else 1,
                )
                phase = (i + 0.5) / max(1, len(names))
                xs = [2 ** ((k + phase) * math.log2(right) / 4) for k in range(4)]
                counts = [sum(r <= x for r in profile["ratios"][method]) for x in xs]
                n = profile["n"] if kind == "full" else conditional["n"]
                ys = (
                    [
                        k / n if kind == "full" else math.log((k + 0.5) / (n - k + 0.5))
                        for k in counts
                    ]
                    if n
                    else [math.nan] * len(xs)
                )
                ax.plot(
                    xs,
                    ys,
                    linestyle="none",
                    color=color,
                    marker=marker,
                    markersize=3,
                    markerfacecolor="white",
                    markeredgewidth=0.65,
                )
            ax.set_xscale("log", base=2)
            ax.set_xlim(*views[kind + "_xlim"])
            ax.set_ylim(*views[kind + "_ylim"])
            exponent = int(math.log2(right))
            ax.set_xticks([2**k for k in range(0, exponent + 1, max(1, math.ceil(exponent / 5)))])
            ax.xaxis.set_major_formatter(FuncFormatter(lambda x, _: f"{x:g}"))
            if kind == "full":
                ax.set_yticks([0, 0.5, 1])
                ax.set_title(title, loc="left")
            else:
                ticks, tick_labels = conditional_logit_ticks(n)
                ax.set_yticks(ticks, tick_labels)
                ax.axhline(0, color="#A9AFB4", linewidth=0.5)
                ax.set_xlabel(
                    "Ratio to fastest successful method"
                    if metric == "seconds"
                    else "Ratio to fewest gradients"
                )
                ax.set_title(
                    f"Conditional on ≥1 success · N={n}", loc="left", fontsize=7.2, color="#626B71"
                )
            if not col:
                ax.set_ylabel("Fraction" if kind == "full" else "Conditional solved")
            ax.grid(True, alpha=0.8)
            ax.set_axisbelow(True)
            if not n:
                ax.text(
                    0.5, 0.5, "No recorded success", transform=ax.transAxes, ha="center", fontsize=7
                )
    handles = [
        Line2D(
            [],
            [],
            color=STYLE.get(m, (f"C{i % 10}", "--", "o"))[0],
            linestyle=STYLE.get(m, ("", "--", "o"))[1],
            marker=STYLE.get(m, ("", "", "o"))[2],
            markerfacecolor="white",
            markersize=3,
            linewidth=1.8 if m in ("XR", "XR-F") else 1,
        )
        for i, m in enumerate(names)
    ]
    fig.legend(
        handles,
        [labels.get(m, m) for m in names],
        loc="lower center",
        ncol=min(4, len(names)),
        frameon=False,
        columnspacing=1.5,
        handlelength=3,
        bbox_to_anchor=(0.5, 0.005),
    )
    fig.subplots_adjust(
        left=0.09,
        right=0.985,
        top=0.92 if missing_count else 0.94,
        bottom=0.20,
        hspace=0.43,
        wspace=0.26,
    )
    if missing_count:
        fig.text(
            0.99, 0.995, "INCOMPLETE CAMPAIGN", ha="right", va="top", color="#A94444", fontsize=7
        )
    path = output / "figures/libsvm.pdf"
    fig.savefig(
        path, metadata={"Creator": "XR reproducible study", "CreationDate": None, "ModDate": None}
    )
    plt.close(fig)
    return path


def render(
    records: Sequence[Mapping[str, Any]],
    output_dir: str | Path,
    *,
    expected_methods: Sequence[str] | Mapping[str, Sequence[str]] | None = None,
    expected_problems: Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Create three vector figures, direct TeX tables, and an honest result report.

    Pass the frozen campaign's complete problem metadata and methods to expose
    missing work even if an entire scheduled problem produced no result.  The
    return value contains completeness and file sizes for the CLI, not raw data.
    No binary dataset, image raster, or duplicate solver history is generated.
    """
    records = list(records)
    _index(records)
    _validate_aliases(records)
    output = Path(output_dir)
    manifest_path = output / "manifest.json"
    manifest = json.loads(manifest_path.read_text()) if manifest_path.is_file() else {}
    (output / "figures").mkdir(parents=True, exist_ok=True)
    (output / "tables").mkdir(parents=True, exist_ok=True)
    cohort = _cohort(records, expected_problems)
    unknown_groups = {p.get("group") for p in cohort if p["suite"] == "cutest"} - {
        *CUTEST_GROUPS,
        "quadratic",
    }
    if unknown_groups:
        raise ValueError(f"Unclassified CUTEst groups: {sorted(unknown_groups, key=str)}")
    methods = _methods_by_suite(records, expected_methods, cohort)
    labels = {r["method"]: r.get("label", r["method"]) for r in records}
    summaries = _summary_rows(records, cohort, methods, labels)
    missing_count = sum(s["missing"] for s in summaries)
    artifacts = _plots(records, cohort, methods, labels, output, missing_count)

    libsvm_analysis = _libsvm_tables(records, cohort, methods.get("libsvm", []), labels, output)
    artifacts.extend(libsvm_analysis["artifacts"])
    for suite in methods:
        rows = [
            [
                _tex(s["label"]),
                f"{s['success']}/{s['n']}",
                str(s["wins"]),
                _number(s["n_g"]),
                _number(s["n_f"]),
                _number(s["seconds"]),
            ]
            for s in summaries
            if s["suite"] == suite
        ]
        path = output / "tables" / f"{suite}_summary.tex"
        _table(
            path,
            "lrrrrr",
            ["Method", "Solved", "Wins", "$N_g$", "$N_f$", "Seconds"],
            rows,
            f"{_tex(SUITE_LABELS.get(suite, suite))} results. Wins include exact ties. "
            "Costs are geometric means over that method's successful instances; "
            "their denominators may differ, so pairwise comparisons are reported separately. "
            "Function and gradient evaluations are both actual backend counts; a gradient "
            "profile alone is not a total-work claim.",
            f"tab:xr-{suite}",
        )
        artifacts.append(path)

    group_counts = Counter((p["suite"], p.get("group") or "--") for p in cohort)
    path = output / "tables" / "problems.tex"
    _table(
        path,
        "llr",
        ["Suite", "Group", "Instances"],
        [[_tex(s), _tex(g), str(n)] for (s, g), n in sorted(group_counts.items())],
        "Frozen benchmark cohort. Repeated dimensions of one family are separate instances.",
        "tab:xr-problems",
    )
    artifacts.append(path)

    diagnostic_rows = _diagnostics(records)
    if diagnostic_rows:
        path = output / "tables" / "diagnostics.tex"
        _table(
            path,
            "llrrrrrr",
            [
                "Group",
                "Method",
                "Solved/run",
                "$w$",
                "$m$",
                "Rank/1k$g$",
                "Drop/1k$g$",
                "F pass/fail",
            ],
            [
                [
                    _tex(s["group"]),
                    _tex(s["method"]),
                    f"{s['solved']}/{s['completed']}",
                    _number(s["window"]),
                    _number(s["capacity"]),
                    _number(s["rank_per_1000g"]),
                    _number(s["window_per_1000g"]),
                    f"{s['counters'].get('nF_applied', 0)}/{s['counters'].get('nF_fallback', 0)}",
                ]
                for s in diagnostic_rows
            ],
            "Observed primary-XR diagnostics, including stopped and capped runs. "
            "$w$ is the median per-run mean retained window; $m$ is the median largest "
            "memory capacity. Deletions are totals per 1000 actual gradients. F pass/fail "
            "counts nonzero corrected-model gate decisions. Stop reasons, complete "
            "counters and any available spectral bounds are retained in the report.",
            "tab:xr-diagnostics",
        )
        artifacts.append(path)

    family_rows = _family_sensitivity(records, cohort, methods.get("cutest", []))
    if family_rows:
        path = output / "tables" / "cutest_family_sensitivity.tex"
        _table(
            path,
            "llrrrrr",
            ["Group", "Method", "$N$", "Families", "Raw win", "Family win", "Family solved"],
            [
                [
                    _tex(s["group"]),
                    _tex(labels.get(s["method"], s["method"])),
                    str(s["n"]),
                    str(s["families"]),
                    _number(100 * s["raw_win"]),
                    _number(100 * s["family_win"]),
                    _number(100 * s["family_solved"]),
                ]
                for s in family_rows
            ],
            "CUTEst sensitivity to family weighting (percent). Raw wins use equal instance "
            "weights. Family-balanced wins and solved fractions give each explicit CUTEst "
            "source family equal total weight within its panel. Wins include ties; failed "
            "and missing instances retain their denominator weight. Costs are gradient evaluations.",
            "tab:xr-family-sensitivity",
        )
        artifacts.append(path)

    development_rows = _development_sensitivity(records, cohort, methods.get("cutest", []))
    if development_rows:
        path = output / "tables" / "cutest_development_sensitivity.tex"
        _table(
            path,
            "llrrrr",
            ["Stratum", "Method", "$N$", "Families", "Family solved", "Family win"],
            [
                [
                    _tex(s["role"]),
                    _tex(labels.get(s["method"], s["method"])),
                    str(s["n"]),
                    str(s["families"]),
                    _number(100 * s["family_solved"]),
                    _number(100 * s["family_win"]),
                ]
                for s in development_rows
            ],
            "Prespecified development-role sensitivity (percent), with equal source-family "
            "weight within each stratum. All three strata are retained, including failures. "
            "Remaining benchmark cases are not an independent held-out validation set; "
            "earlier development already exposed parts of this benchmark.",
            "tab:xr-development-sensitivity",
        )
        artifacts.append(path)

    grid = _perturbed_grid(records, cohort)
    if grid:
        rows = []
        for kappa in grid["kappas"]:
            for epsilon in grid["epsilons"]:
                cell = grid["cells"][kappa, epsilon]
                ratio = 2 ** cell["logratio"] if cell["logratio"] is not None else None
                rows.append(
                    [
                        _number(kappa),
                        _number(epsilon),
                        f"{cell['paired']}/{cell['n']}",
                        _number(ratio),
                        str(cell["ours_only"]),
                        str(cell["other_only"]),
                    ]
                )
        path = output / "tables" / "perturbations.tex"
        _table(
            path,
            "rrrrrr",
            [r"$\kappa$", r"$\epsilon$", "Paired", "L-BFGS/XR-F", "XR-F only", "L-BFGS only"],
            rows,
            "Complete perturbation grid. Ratios are the exponential of the median "
            "log gradient-cost ratio on jointly successful seeds; above one favors XR-F. "
            "The paired denominator and exclusive successes retain all failed seeds.",
            "tab:xr-perturbations",
        )
        artifacts.append(path)

    paired = []
    if "ablation" in methods:
        names = methods["ablation"]
        base = "XR-F" if "XR-F" in names else names[0]
        problems = [p["problem"] for p in cohort if p["suite"] == "ablation"]
        rows = []
        for method in names:
            comparison = _paired(records, problems, base, method, suite="ablation")
            summary = next(
                s for s in summaries if s["suite"] == "ablation" and s["method"] == method
            )
            rows.append(
                [
                    _tex(labels.get(method, method)),
                    f"{summary['success']}/{summary['n']}",
                    _number(comparison["ratio"]),
                    str(comparison["paired"]),
                    str(comparison["ours_only"]),
                    str(comparison["other_only"]),
                ]
            )
        path = output / "tables" / "ablations.tex"
        _table(
            path,
            "lrrrrr",
            ["Variant", "Solved", "Cost/base", "Paired", "Base only", "Variant only"],
            rows,
            "One-factor ablations. Cost/base is the geometric mean gradient-cost "
            f"ratio against {_tex(labels.get(base, base))} on jointly solved instances. "
            "Values above one favor the base; success differences are retained explicitly.",
            "tab:xr-ablations",
        )
        artifacts.append(path)

    cutest_problems = [p["problem"] for p in cohort if p["suite"] == "cutest"]
    for ours in ("XR", "XR-F"):
        if ours in methods.get("cutest", []):
            for other in methods["cutest"]:
                if other not in ("XR", "XR-F"):
                    paired.append(_paired(records, cutest_problems, ours, other))
    contexts, distinct_pairs = _context_counts(cohort)
    aliased_records = sum(bool(r.get("alias_of")) for r in records)
    lines = [
        "# XR experiment report",
        "",
        f"Campaign completeness: **{'PARTIAL' if missing_count else 'COMPLETE'}**. "
        f"{len(records)} completed comparison records, {contexts} study contexts, "
        f"{missing_count} missing scheduled runs.",
        "",
        f"The contexts represent **{distinct_pairs} distinct objective/start pairs**; "
        f"{contexts - distinct_pairs} contexts reuse a primary objective/start for ablations. "
        "These are not independent benchmark problems. "
        f"{len(records) - aliased_records} computed observations and {aliased_records} exact "
        "alias rows supply the completed comparisons.",
        "",
        "This report is computed from the frozen run history. Campaign-phase provenance "
        "and ablation aliases are disclosed below. No retrospective objective evaluations "
        "or outcome-based exclusions are used.",
        "",
        "## Coverage and success",
        "",
        "| Suite | Method | Solved | Wins incl. ties | Missing | Mean Ng | Mean Nf |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    lines += [
        f"| {s['suite']} | {s['label']} | {s['success']}/{s['n']} | {s['wins']} | {s['missing']} | "
        f"{_number(s['n_g'])} | {_number(s['n_f'])} |"
        for s in summaries
    ]
    lines += [
        "",
        "Mean counts in this table are geometric means over each method's "
        "successful instances, whose denominators can differ. They are descriptive, "
        "not an unconditional ranking. Gradient profiles alone are not total-work claims.",
        "TeX tables move columns constant across every row into an explicit caption "
        "statement, retaining their exact values and any common failures. This report "
        "and the bounded history retain the complete counts.",
    ]
    lines += libsvm_analysis["report"]
    findings = _qualitative_findings(records, cohort, methods, complete=not missing_count)
    if findings:
        lines += ["", "## Qualitative interpretation", ""]
        for paragraph in findings:
            lines += [paragraph, ""]
    total_cutest = sum(p["suite"] == "cutest" for p in cohort)
    main_cutest = sum(p["suite"] == "cutest" and p.get("group") in CUTEST_GROUPS for p in cohort)
    if total_cutest:
        lines += [
            "",
            f"CUTEst summary and paired tables include all {total_cutest} instances. "
            f"The four main profile panels contain {main_cutest} nonquadratic-classified "
            f"instances; {total_cutest - main_cutest} explicitly classified quadratics "
            "remain in the summary and supplementary accounting rather than those "
            "four panels.",
        ]
    controlled = []
    for suite in ("quadratic", "perturbed"):
        problems = [p["problem"] for p in cohort if p["suite"] == suite]
        if not problems:
            continue
        for ours in ("XR", "XR-F"):
            if ours not in methods.get(suite, []):
                continue
            for other in methods[suite]:
                if other in ("XR", "XR-F"):
                    continue
                comparison = _paired(records, problems, ours, other, suite=suite)
                comparison["suite"] = suite
                controlled.append(comparison)
    if controlled:
        lines += [
            "",
            "## Controlled-family paired gradient costs",
            "",
            "Ratios are competitor/our-method geometric means on jointly solved "
            "instances. All original competitors are shown; exclusive successes "
            "and joint denominators remain explicit. These are results on the "
            "specified controlled families, not a universal performance claim.",
            "",
            "| Suite | Our method | Competitor | Ratio | Jointly solved | Ours only | Competitor only |",
            "|---|---|---|---:|---:|---:|---:|",
        ]
        lines += [
            f"| {s['suite']} | {s['ours']} | {s['other']} | {_number(s['ratio'])} | "
            f"{s['paired']} | {s['ours_only']} | {s['other_only']} |"
            for s in controlled
        ]
    if family_rows:
        lines += [
            "",
            "## Family-balanced sensitivity",
            "",
            "Each CUTEst source family has equal total weight within its panel; "
            "instances within that family share its weight. Family names come only "
            "from explicit problem metadata. Failures and missing runs keep their weight. "
            "The main profiles continue to weight all instances equally.",
            "",
            "| Group | Method | Instances | Families | Raw wins % | Family wins % | Family solved % |",
            "|---|---|---:|---:|---:|---:|---:|",
        ]
        lines += [
            f"| {s['group']} | {labels.get(s['method'], s['method'])} | {s['n']} | "
            f"{s['families']} | {_number(100 * s['raw_win'])} | "
            f"{_number(100 * s['family_win'])} | {_number(100 * s['family_solved'])} |"
            for s in family_rows
        ]
    elif any(p["suite"] == "cutest" for p in cohort):
        lines += [
            "",
            "Family-balanced sensitivity is unavailable: complete explicit CUTEst "
            "source-family metadata were not supplied. No family is inferred from names.",
        ]
    if cutest_problems:
        names = methods.get("cutest", [])
        profile = performance_profiles(records, names, cutest_problems)
        lines += [
            "",
            f"CUTEst instances on which all compared methods failed: "
            f"**{len(profile['all_failed'])}/{len(cutest_problems)}**. "
            "These instances remain in every ordinary-profile denominator; the "
            "conditional logit panels explicitly exclude them.",
        ]
    if paired:
        lines += [
            "",
            "## Paired CUTEst gradient costs",
            "",
            "Ratio is competitor/XR on jointly successful instances. Above one favors "
            "XR. The next columns expose success differences outside this paired subset.",
            "",
            "| Our method | Competitor | Ratio | Jointly solved | Ours only | Competitor only | Neither |",
            "|---|---|---:|---:|---:|---:|---:|",
        ]
        lines += [
            f"| {p['ours']} | {p['other']} | {_number(p['ratio'])} | {p['paired']} | "
            f"{p['ours_only']} | {p['other_only']} | {p['neither']} |"
            for p in paired
        ]
    if development_rows:
        lines += [
            "",
            "## Prespecified development-role sensitivity",
            "",
            "These strata were labeled by family before the final frozen run. "
            "The remaining-benchmark stratum is a sensitivity check, not an independent "
            "held-out validation claim. Every stratum, including its failures, is shown.",
            "",
            "| Stratum | Method | Instances | Families | Family solved % | Family wins % |",
            "|---|---|---:|---:|---:|---:|",
        ]
        lines += [
            f"| {s['role']} | {labels.get(s['method'], s['method'])} | {s['n']} | "
            f"{s['families']} | {_number(100 * s['family_solved'])} | "
            f"{_number(100 * s['family_win'])} |"
            for s in development_rows
        ]
    status_counts = Counter(str(r.get("status", "unspecified")) for r in records)
    computed_status_counts = Counter(
        str(r.get("status", "unspecified")) for r in records if not r.get("alias_of")
    )
    lines += ["", "## Timing and reproducibility", ""]
    renderer_path = Path(__file__).resolve()
    renderer_hash = hashlib.sha256(renderer_path.read_bytes()).hexdigest()
    lines += [
        f"Rendering source: [study.py]({os.path.relpath(renderer_path, output)}), "
        f"SHA-256 `{renderer_hash}`. Matplotlib `{version('matplotlib')}`. "
        "This rendering fingerprint is separate from the frozen scientific-source "
        "fingerprint.",
        "",
    ]
    if manifest:
        lines += _timing_description(manifest)
        lines += [
            f"Current scientific-source fingerprint: `{manifest.get('source_hash', 'unspecified')}`. "
            f"Protocol: `{manifest.get('protocol', 'unspecified')}`. "
            f"Target: `{manifest.get('target', 'unspecified')}`.",
            "",
        ]
        lines += _native_provenance(manifest, output)
        refresh = manifest.get("baseline_timing_refresh") or {}
        if refresh:
            lines += [
                "Final baseline timing refresh: "
                f"{refresh.get('recomputed_cutest_baselines', 'unspecified')} CUTEst "
                "competitor observations were remeasured unconditionally with the "
                "final frozen scientific source; "
                f"{refresh.get('retained_current_source_observations', 'unspecified')} "
                "already completed observations from that same source were retained. "
                "Targets, budgets and declared worker load were unchanged; earlier "
                "baseline observations were not selected or substituted by outcome.",
                "",
                "Refresh policy: " + str(refresh.get("policy", "see manifest")),
                "",
            ]
        if manifest.get("cohort_policy"):
            policy = manifest["cohort_policy"]
            lines += [
                "Cohort/development policy: "
                + (policy if isinstance(policy, str) else json.dumps(policy, ensure_ascii=False)),
                "",
            ]
        kernel = manifest.get("kernel_optimization") or {}
        if kernel:
            kernel_path = Path(__file__).resolve().parents[2] / kernel.get("report", "")
            lines += [
                "Historical Python-kernel optimization policy: "
                + str(kernel.get("policy", "see manifest"))
            ]
            if kernel_path.is_file():
                audit = json.loads(kernel_path.read_text())
                lines += [
                    f"Audit: [kernel-optimization.json]({os.path.relpath(kernel_path, output)}), "
                    f"SHA-256 `{hashlib.sha256(kernel_path.read_bytes()).hexdigest()}`; "
                    f"optimized scientific fingerprint `{audit.get('optimized_source_hash', 'unspecified')}`. "
                    "This historical Python-kernel audit is not evidence about "
                    "the C port's floating-point trajectory. It is separate from "
                    "the measured benchmark timings and is not used to rescale them."
                ]
            lines.append("")
        if manifest.get("aliases"):
            lines += [
                f"The manifest schedules {len(manifest.get('jobs', []))} actual solver "
                f"runs and {len(manifest['aliases'])} exact ablation aliases. Alias "
                "rows reuse their primary observations without another optimization "
                "run and are not additional statistical replications.",
                "",
            ]
        reuse = manifest.get("baseline_reuse") or {}
        if reuse:
            producers = Counter(
                row.get("producer_source_hash", "unspecified") for row in reuse.get("records", [])
            )
            lines += [
                f"The final manifest seeds **{sum(producers.values())} reused CUTEst "
                "baseline observations**. All own-method and synthetic observations "
                "were discarded and run with the current practical version. Reuse is "
                "restricted to unchanged baseline/oracle/problem dependencies, checked "
                "by producer SHA-256 fingerprints and recorded semantic conditions "
                "(parameters, targets, budgets, environment and worker load). Each reused "
                "row retains its actual producer fingerprint; no common raw source hash "
                "is asserted for the combined history.",
                "",
                "Reuse policy: " + str(reuse.get("policy", "recorded in manifest")),
                "",
            ]
            lines += [
                f"- Producer `{producer}`: {count} observations."
                for producer, count in sorted(producers.items())
            ]
            lines.append("")
        for revision in manifest.get("revisions", []):
            lines += [
                f"Recorded source revision from `{revision.get('prior_source_hash', 'unspecified')}`: "
                f"{revision.get('reused_baseline_records', 0)} baseline records were reused; "
                f"{revision.get('discarded_our_records', 0)} earlier own-method observations "
                "were discarded regardless of success and rerun. The revision record "
                "documents byte-identical baseline implementations, shared oracle, "
                "problems and presets for any permitted reuse. The current aggregate "
                "fingerprint is not asserted to be the raw source fingerprint of every "
                "reused observation.",
                "",
                str(revision.get("reason", "")),
                "",
            ]
    else:
        lines += [
            "No campaign manifest was found beside this report; concurrency and "
            "the execution environment cannot be established from run rows alone.",
            "",
        ]
    lines += _implementation_description(manifest)
    if diagnostic_rows:
        lines += [
            "",
            "## XR diagnostics and unresolved cases",
            "",
            "Diagnostics include successful, method-stopped, budget-limited and timed-out "
            "runs whenever their final counters were returned. Missing counters are not "
            "invented; the diagnosed/completed column states availability.",
            "",
            "| Group | Method | Diagnosed/run | Median mean window | Median max cap | Median lower bound | Median upper bound | Max upper bound |",
            "|---|---|---:|---:|---:|---:|---:|---:|",
        ]
        lines += [
            f"| {s['group']} | {s['method']} | {s['diagnosed']}/{s['completed']} | "
            f"{_number(s['window'])} | {_number(s['capacity'])} | {_number(s['lower'])} | "
            f"{_number(s['upper'])} | {_number(s['upper_max'])} |"
            for s in diagnostic_rows
        ]
        lines += [
            "",
            "A dash means no bound was computed or returned; it is not a zero "
            "bound. Historical Ritz bounds are unnecessary for the practical secant "
            "policy; midpoint diagnostics can retain them. Totals below count actual "
            "returned model events, not independent "
            "problems.",
            "",
        ]
        for summary in diagnostic_rows:
            counters = ", ".join(
                f"{key}={value:g}" for key, value in sorted(summary["counters"].items())
            )
            reasons = "; ".join(
                f"{reason}={count}" for reason, count in sorted(summary["reasons"].items())
            )
            lines += [
                f"- **{summary['group']} / {summary['method']}**: {reasons}. "
                f"Returned counters: {counters or 'unavailable'}."
            ]
        findings = Path(__file__).resolve().parents[2] / "docs" / "NumericalFindings.md"
        practical = findings.with_name("PracticalVariant.md")
        lines += [
            "",
            f"The historical-midpoint numerical mechanism is analyzed in "
            f"[NumericalFindings.md]({os.path.relpath(findings, output)}); "
            f"the practical policy and its theoretical scope are described in "
            f"[PracticalVariant.md]({os.path.relpath(practical, output)}). "
            "The algebraic example does not establish that every observed failure "
            "has that mechanism, and a conditional convergence theorem does not "
            "replace the empirical failure counts.",
        ]
    lines += [
        "",
        "## Per-method CUTEst stops",
        "",
        "| Method | Completed | Recorded statuses and stop reasons |",
        "|---|---:|---|",
    ]
    for method in methods.get("cutest", []):
        completed = [r for r in records if r["suite"] == "cutest" and r["method"] == method]
        reasons = Counter(
            str(r.get("status", "unspecified"))
            + (
                ": " + str((r.get("info") or {})["stop"])
                if not _successful(r) and (r.get("info") or {}).get("stop")
                else ""
            )
            for r in completed
        )
        lines.append(
            f"| {labels.get(method, method)} | {len(completed)} | "
            + "; ".join(f"{key}: {value}" for key, value in sorted(reasons.items()))
            + " |"
        )
    lines += [
        "",
        "## Status accounting",
        "",
        "Computed observations are actual solver runs; their provenance is stated "
        "above. Comparison rows also include exact ablation aliases; aliases are "
        "not additional independent runs.",
        "",
        "| Status | Computed observations | Comparison rows including aliases |",
        "|---|---:|---:|",
        *[
            f"| {status} | {computed_status_counts.get(status, 0)} | {count} |"
            for status, count in sorted(status_counts.items())
        ],
        "",
        "## Figure conventions",
        "",
        "LIBSVM uses one four-panel figure: gradient and wall-time ratios each have "
        "ordinary and conditional empirical-logit scales over all scheduled objectives. "
        "Each CUTEst group has an ordinary Dolan–Moré profile and an empirical-logit "
        "companion over the same full base-two logarithmic ratio range. The ordinary "
        "profile retains all scheduled instances, including all-method failures, "
        "and its success plateau may remain below one. The companion is explicitly "
        "conditional on at least one compared method having succeeded: its denominator "
        "N excludes only the all-method failures and is printed above the panel. It "
        "recomputes rho on that cohort and displays log((N*rho+0.5)/"
        "(N*(1-rho)+0.5)), with a half-count display correction at the endpoints. "
        "Its vertical ticks show the original conditional percentages: 0%, 50% "
        "and 100%, with 90% and then 99% added only when each is at least 14% "
        "of the complete vertical span from the other labels. "
        "An individual method's failed or missing run still has infinite ratio. "
        "Every finite ratio remains visible in both panels; no probability is moved "
        "or failure assigned a finite cost. Distinct colors, two line-style families "
        "and sparse log-spaced markers identify overlaps.",
        "",
        "The controlled figure has two panels. Its trajectory uses the lexicographically first frozen problem "
        "in the quadratic suite, selected independently of outcomes. It shows XR, XR-F, "
        "L-BFGS, L-CG_DESCENT and MS-L-BFGS when present. Complete numerical coverage "
        "is retained in the suite summary tables. Curves show the best observed reference-energy "
        "error or gradient norm over actual queries, including rejected trial points; they "
        "are not accepted-iterate trajectories. Each curve is normalized by its first "
        "positive recorded value. The synthetic reference energy uses the specified base "
        "matrix A, which need not equal the perturbed objective's stationary Hessian. "
        "Exact zeros are displayed one fifth below the smallest positive recorded value. "
        "The common vertical quantity is identical for every method in each panel.",
        "",
        "When kappa/epsilon metadata are supplied, the perturbation panel uses the "
        "entire frozen grid and all seeds: color is the median log2 gradient-cost ratio "
        "L-BFGS/XR-F on jointly successful seeds. Blue favors XR-F. Cell text gives "
        "the corresponding cost ratio and jointly successful/total seeds. If every "
        "cell has the same completely solved seed count with no exclusive successes, "
        "that count moves to the shared panel title and the ratio text is enlarged; "
        "otherwise all per-cell denominators remain visible. (+a,−b) "
        "lists XR-F-only and L-BFGS-only successes. Failed seeds are never converted "
        "to artificial finite costs. The dense accepted-iterate local study is a "
        "separate artifact, with its own manifest, error norm and report. No "
        "Q-order exponent is fitted: the article's local guarantee is an R-order "
        "bound, not an observed consecutive-error slope.",
        "",
        "Reference: Dolan and Moré, *Benchmarking Optimization Software with "
        "Performance Profiles*, Mathematical Programming 91 (2002), 201–213; "
        "https://doi.org/10.1007/s101070100263; https://arxiv.org/abs/cs/0102001.",
        "",
        "## Artifacts",
        "",
    ]
    formal = manifest.get("formal_reference") or {}
    if formal:
        lines += [
            "Formal reference scope: " + str(formal.get("scope", "see manifest")),
            "",
            f"Lean version: `{formal.get('lean_version', 'unspecified')}`; "
            "recorded axioms: "
            + ", ".join(f"`{axiom}`" for axiom in formal.get("used_axioms", []))
            + ".",
        ]
        workspace = Path(__file__).resolve().parents[3]
        for file, fingerprint in formal.get("files", {}).items():
            link = os.path.relpath(workspace / file, output)
            lines += [f"- [{file}]({link}), SHA-256 `{fingerprint}`."]
        lines += [
            "",
            "These are exact-real definitions and theorems. The floating-point "
            "Python/BLAS execution and unconditional local fast rates are not "
            "certified by that reference.",
            "",
        ]
    for name, description in (
        ("supplement", "Supplementary comparisons"),
        ("local", "Dense accepted-iterate local diagnostic"),
        ("settings", "Fixed-setting sensitivity"),
    ):
        linked_report = output.parent / name / "REPORT.md"
        if linked_report.is_file():
            lines += [f"{description}: [REPORT.md]({os.path.relpath(linked_report, output)}).", ""]
    verification = output / "logs" / "verification.log"
    if verification.is_file():
        lines += ["Reproduction checks: [verification.log](logs/verification.log).", ""]
    total_bytes = 0
    for artifact in artifacts:
        size = artifact.stat().st_size
        total_bytes += size
        lines.append(f"- `{artifact.relative_to(output)}` ({size:,} bytes)")
    if total_bytes > 10 * 1024 * 1024:
        raise ValueError("Figure/table output exceeded the 10 MiB compact-artifact budget")
    report_path = output / "REPORT.md"
    report_path.write_text("\n".join(_compact_markdown_tables(lines)) + "\n", encoding="utf-8")
    artifacts.append(report_path)
    return {
        "complete": not missing_count,
        "records": len(records),
        "problems": len(cohort),
        "missing": missing_count,
        "summary": summaries,
        "paired": paired,
        "family_sensitivity": family_rows,
        "development_sensitivity": development_rows,
        "diagnostics": diagnostic_rows,
        "controlled_comparisons": controlled,
        "libsvm_comparisons": libsvm_analysis["comparisons"],
        "libsvm_outcomes": libsvm_analysis["outcomes"],
        "artifacts": [str(p) for p in artifacts],
        "bytes": sum(p.stat().st_size for p in artifacts),
    }


def _local_accuracy_statistics(rows: Sequence[Mapping], config: Mapping) -> dict:
    """Accepted-only first hits; all frozen contexts enter every quantile.

    Quantiles are inverse empirical-CDF order statistics, so an unattained
    target remains infinity instead of disappearing or receiving a cap cost.
    """
    cases = [
        (n, float(k), seed)
        for n in config["dimensions"]
        for k in config["condition_numbers"]
        for seed in config["seeds"]
    ]
    methods = config.get("methods", ["XR", "XR-F"])
    index = {}
    for row in rows:
        key = (row["n"], float(row["kappa"]), row["seed"], row["method"])
        if key in index:
            raise ValueError("Duplicate local-study observation")
        if key[:3] not in cases or key[3] not in methods:
            raise ValueError("Unexpected local-study observation")
        trace = row["trace"]
        if not trace or [p["iteration"] for p in trace] != list(range(len(trace))):
            raise ValueError("Local study must retain every accepted iterate")
        if "accepted" in row and row["accepted"] != len(trace) - 1:
            raise ValueError("Local study accepted count disagrees with its dense trace")
        if any(not math.isfinite(p["error"]) or p["error"] < 0 for p in trace):
            raise ValueError("Local errors must be finite and nonnegative")
        if any(not math.isfinite(p["n_g"]) or p["n_g"] < 1 for p in trace):
            raise ValueError("Local gradient counts must be positive and finite")
        if any(a["n_g"] > b["n_g"] for a, b in zip(trace, trace[1:])):
            raise ValueError("Local gradient counts must be chronological")
        index[key] = row
    digits = list(range(2, 13, 2))
    stats = {}
    for method in methods:
        stats[method] = []
        for digit in digits:
            costs = []
            for n, kappa, seed in cases:
                row = index.get((n, kappa, seed, method))
                trace = row["trace"] if row else []
                costs.append(
                    next((p["n_g"] / n for p in trace if p["error"] <= 10.0**-digit), math.inf)
                )
            ordered = sorted(costs)

            def quantile(q):
                return ordered[max(0, math.ceil(q * len(ordered)) - 1)] if ordered else math.inf

            stats[method].append(
                dict(
                    digit=digit,
                    q25=quantile(0.25),
                    median=quantile(0.5),
                    q75=quantile(0.75),
                    attained=sum(math.isfinite(c) for c in costs),
                    n=len(cases),
                )
            )
    return dict(
        cases=cases,
        methods=methods,
        index=index,
        digits=digits,
        statistics=stats,
        missing=len(cases) * len(methods) - len(index),
    )


def render_local_study(rows: Sequence[Mapping], output: Path, config: Mapping) -> dict:
    """Two-panel diagnostic from every actual accepted full-memory iterate.

    This is separate from the main benchmark and never changes its frozen
    history, profile targets, timings, or publication tables.
    """
    _prepare_plot_cache()
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D

    data = _local_accuracy_statistics(rows, config)
    output = Path(output)
    (output / "figures").mkdir(parents=True, exist_ok=True)
    (output / "tables").mkdir(parents=True, exist_ok=True)
    plt.rcParams.update(
        {
            "pdf.fonttype": 42,
            "font.family": "DejaVu Sans",
            "font.size": 8,
            "axes.labelsize": 8,
            "axes.titlesize": 9,
            "axes.linewidth": 0.5,
            "xtick.labelsize": 7.5,
            "ytick.labelsize": 7.5,
        }
    )
    # Fixed endpoint dimensions and the same seed show the actual transition
    # to a full model. Every accepted iterate is plotted, including plateaux.
    fixed_cases = [(5, 100.0, 0), (20, 100.0, 0)]
    selected = {
        (*case, method): data["index"].get((*case, method))
        for case in fixed_cases
        for method in data["methods"]
    }
    positives = [
        p["error"] for row in selected.values() if row for p in row["trace"] if p["error"] > 0
    ]
    floor = min(positives, default=1e-12) * 0.2
    max_iteration = max(
        (p["iteration"] for row in selected.values() if row for p in row["trace"]), default=1
    )
    fig, axes = plt.subplots(1, 2, figsize=(7.1, 3.35), sharex=True, sharey=True)
    trajectory_cases = []
    safeguard_seen = False
    for axis, case in zip(axes, fixed_cases):
        n, kappa, seed = case
        first_full = {}
        available = False
        for method in data["methods"]:
            row = selected[(*case, method)]
            if row is None:
                continue
            available = True
            trace = row["trace"]
            color, _, marker = STYLE.get(method, ("#666666", "-", "o"))
            x = [p["iteration"] for p in trace]
            y = [max(p["error"], floor) for p in trace]
            axis.plot(
                x,
                y,
                color=color,
                linewidth=1.5,
                marker=marker,
                markersize=3.5,
                markerfacecolor="white",
                markeredgewidth=0.75,
            )
            full = [p for p in trace if p.get("full_window")]
            if full:
                first_full[method] = full[0]["iteration"]
                axis.plot(
                    [p["iteration"] for p in full],
                    [max(p["error"], floor) for p in full],
                    linestyle="none",
                    marker=marker,
                    markersize=3.8,
                    markerfacecolor=color,
                    markeredgecolor=color,
                )
            events = 0
            for previous, point in zip(trace, trace[1:]):
                if point.get("counters", {}).get("nsafe", 0) > previous.get("counters", {}).get(
                    "nsafe", 0
                ):
                    axis.plot(
                        point["iteration"],
                        max(point["error"], floor),
                        marker="x",
                        color="#222222",
                        markersize=5,
                        linestyle="none",
                    )
                    events += 1
                    safeguard_seen = True
            trajectory_cases.append(
                dict(
                    n=n,
                    kappa=kappa,
                    seed=seed,
                    method=method,
                    accepted_points=len(trace),
                    first_full_iteration=first_full.get(method),
                    safeguard_events=events,
                )
            )
        if len(first_full) == len(data["methods"]) and len(set(first_full.values())) == 1:
            first = next(iter(first_full.values()))
            axis.axvline(first, color="#8A9298", linewidth=0.65, linestyle=":")
            note = f"First full window: k={first}"
        elif first_full:
            note = "First full window\n" + "; ".join(f"{m}: k={k}" for m, k in first_full.items())
        else:
            note = "Full window not attained"
        axis.text(
            0.97,
            0.91,
            note,
            ha="right",
            va="top",
            transform=axis.transAxes,
            color="#626B71",
            fontsize=7.2,
        )
        if not available:
            axis.text(
                0.5,
                0.5,
                "Fixed trajectories unavailable",
                ha="center",
                va="center",
                transform=axis.transAxes,
                fontsize=8,
            )
        axis.axhline(config["target"], color="#9CA4A9", linewidth=0.65, linestyle=":")
        axis.set_title(f"$n={n}$", loc="left", fontsize=9)
        axis.set_yscale("log")
        axis.set_xlim(0, max_iteration + 0.75)
        axis.set_ylim(floor, max(1.5, max(positives, default=1) * 1.5))
        axis.set_xlabel(r"Accepted iteration $k$")
        axis.grid(True, color="#E2E5E8", linewidth=0.5)
        axis.tick_params(labelsize=7.5)
        axis.spines[["top", "right"]].set_visible(False)
        axis.set_axisbelow(True)
    axes[0].set_ylabel(r"Relative $H_*$-energy error")
    handles = []
    for method in data["methods"]:
        color, _, marker = STYLE.get(method, ("#666666", "-", "o"))
        handles.append(
            Line2D(
                [],
                [],
                color=color,
                linewidth=1.5,
                marker=marker,
                markersize=4,
                markerfacecolor="white",
                label=method,
            )
        )
    handles.append(
        Line2D(
            [],
            [],
            marker="o",
            linestyle="none",
            color="#555555",
            markersize=4,
            label="full model window",
        )
    )
    if safeguard_seen:
        handles.append(
            Line2D(
                [],
                [],
                marker="x",
                linestyle="none",
                color="#222222",
                markersize=4,
                label="safeguard event",
            )
        )
    fig.legend(
        handles=handles,
        loc="lower center",
        ncol=len(handles),
        frameon=False,
        fontsize=8,
        bbox_to_anchor=(0.5, 0.005),
    )
    fig.suptitle(r"Accepted trajectories: $\kappa=100$, $\epsilon=0.1$, seed 0", fontsize=9, y=0.98)
    fig.subplots_adjust(left=0.09, right=0.985, top=0.83, bottom=0.22, wspace=0.18)
    if data["missing"]:
        fig.text(
            0.99, 0.995, "INCOMPLETE LOCAL STUDY", ha="right", va="top", fontsize=7, color="#A94444"
        )
    figure = output / "figures/local.pdf"
    fig.savefig(
        figure,
        metadata={
            "Creator": "XR accepted-iterate diagnostic",
            "CreationDate": None,
            "ModDate": None,
        },
    )
    plt.close(fig)

    summaries = []
    for n in config["dimensions"]:
        for kappa in config["condition_numbers"]:
            for method in data["methods"]:
                selected = [
                    data["index"].get((n, float(kappa), seed, method)) for seed in config["seeds"]
                ]
                full = [r for r in selected if r and r.get("first_full_n_g") is not None]
                costs = sorted(
                    r["n_g"] / n if r and r.get("success") else math.inf for r in selected
                )
                first = sorted(
                    r["first_full_n_g"] / n
                    if r and r.get("first_full_n_g") is not None
                    else math.inf
                    for r in selected
                )
                middle = max(0, math.ceil(len(selected) / 2) - 1)
                summaries.append(
                    dict(
                        n=n,
                        kappa=kappa,
                        method=method,
                        solved=sum(bool(r and r.get("success")) for r in selected),
                        total=len(selected),
                        full=len(full),
                        cost=costs[middle],
                        first=first[middle],
                    )
                )
    table = output / "tables/local_summary.tex"
    header = [
        r"$n$", r"$\kappa$", "Method", "Target", "Full window",
        r"Med. $N_g/n$", r"First full $N_g/n$",
    ]
    table_rows = [
        [
            str(s["n"]), _number(s["kappa"]), _tex(s["method"]),
            f"{s['solved']}/{s['total']}", f"{s['full']}/{s['total']}",
            _number(s["cost"]), _number(s["first"]),
        ]
        for s in summaries
    ]
    caption = (
        f"Full-memory local study over {len(config['seeds'])} seeds per dimension and condition number. "
        f"The target relative stationary-Hessian norm is ${_math_number(config['target'])}$; "
        rf"$\varepsilon={_math_number(config['epsilon'])}$, initial base energy "
        f"${_math_number(config['initial_base_energy'])}$. Costs are medians of actual "
        r"gradient evaluations divided by $n$. First full is the first accepted "
        r"step whose model uses $n$ retained pairs."
    )
    all_solved_full = bool(summaries) and all(
        s["solved"] == s["full"] == s["total"] for s in summaries
    )
    if all_solved_full:
        header = header[:3] + header[5:]
        table_rows = [row[:3] + row[5:] for row in table_rows]
        caption += (
            f" All {sum(s['total'] for s in summaries)} runs reach the target "
            "and use a full window."
        )
    _table(
        table,
        "rrlrr" if all_solved_full else "rrlrrrr",
        header,
        table_rows,
        caption,
        "tab:xr-local-diagnostic",
    )
    lines = [
        "# Dense accepted-iterate local study",
        "",
        f"Completeness: **{'PARTIAL' if data['missing'] else 'COMPLETE'}**; {len(rows)} observations "
        f"on {len(data['cases'])} frozen contexts, {data['missing']} missing runs.",
        "",
        "Every actual accepted iterate is retained, including the initial point. "
        "Rejected probes cannot satisfy this experiment's target. The diagnostic "
        "error uses the analytic stationary Hessian specified in the manifest, "
        "evaluated in float64; "
        "the Hessian is never supplied to the solver. No competitive wall times "
        "are reported here.",
        "",
        "The two panels use the fixed n=5 and n=20 cases at kappa=100, epsilon=0.1 "
        "and seed=0. Every accepted point is plotted against its actual iteration k; "
        "both axes use the same scales. The first genuinely full retained model "
        "window is labeled in each panel. The dimension endpoints and common seed "
        "are selected independently of observed performance.",
        "",
        "The trajectories are shown without subsampling. Filled markers identify accepted steps using "
        "a window of n retained pairs; a safeguard may still override the model "
        "trial. Crosses identify a safeguard event during that outer iteration. "
        "Curves join recorded points without smoothing or "
        "R-order estimation. Exact zero errors are shown at a display floor "
        "one fifth below the smallest positive error.",
        "",
        "The complete 120-run cohort remains in the summary table. The following "
        "accuracy-cost quantiles are inverse empirical-CDF order statistics over "
        "all 60 contexts per method, including unattained/missing cases at infinity. "
        "They summarize the whole cohort rather than either displayed trajectory. "
        "No failure is assigned a finite cost.",
        "",
        "| Digits | Method | Attained | Q25 Ng/n | Median Ng/n | Q75 Ng/n |",
        "|---:|---|---:|---:|---:|---:|",
    ]
    for method, values in data["statistics"].items():
        lines += [
            f"| {s['digit']} | {method} | {s['attained']}/{s['n']} | {_number(s['q25'])} | "
            f"{_number(s['median'])} | {_number(s['q75'])} |"
            for s in values
        ]
    renderer_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    lines += [
        "",
        f"Scientific source fingerprint: `{config.get('source_hash', 'unspecified')}`. "
        f"Local script SHA-256: `{config.get('script_sha256', 'unspecified')}`. "
        f"Renderer SHA-256: `{renderer_hash}`; Matplotlib `{version('matplotlib')}`.",
        "",
        "Artifacts: `figures/local.pdf`, `tables/local_summary.tex`. The exact-real "
        "local theory has separate hypotheses; these plots do not certify those "
        "hypotheses or establish an unconditional fast rate.",
    ]
    report = output / "REPORT.md"
    report.write_text("\n".join(_compact_markdown_tables(lines)) + "\n")
    return dict(
        complete=not data["missing"],
        records=len(rows),
        contexts=len(data["cases"]),
        summaries=summaries,
        statistics=data["statistics"],
        trajectories=trajectory_cases,
        artifacts=[str(figure), str(table), str(report)],
    )
