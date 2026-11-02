#!/usr/bin/env python3
"""Pinned settings sensitivity: 160 new runs and 80 unchanged main references.

No primary preset is replaced and no best-of-settings solver is constructed.
Only oracle-cost comparisons are aggregated across phases; wall times remain
in the raw history. Optimization uses the main campaign's isolated worker and
the same solver imports, oracle, native callbacks and timing boundaries.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = Path(__file__).resolve()
sys.path.insert(0, str(ROOT / "src"))
GROUPS = ("sos-small", "sos-large", "general-small", "general-large")
FAMILIES = ("XR", "XR-F", "L-BFGS", "L-CG_DESCENT", "MS-L-BFGS")


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def base_inputs(folder, *, require_complete):
    from xrbench.campaign import read_history, source_hash, validate_history

    folder = Path(folder).resolve()
    manifest = json.loads((folder / "manifest.json").read_text())
    if manifest["source_hash"] != source_hash():
        raise ValueError("Main campaign source/configuration changed")
    rows = read_history(folder / "history.jsonl")
    validate_history(rows, manifest)
    scheduled = {job["id"] for job in manifest["jobs"]}
    present = {row["job_id"] for row in rows}
    if present - scheduled or require_complete and present != scheduled:
        raise ValueError("Complete main campaign required before settings execution")
    return folder, manifest, rows


def select_problems(base):
    from xrbench.campaign import digest

    problems = []
    for group in GROUPS:
        candidates = [p for p in base["problems"] if p["suite"] == "cutest" and p["group"] == group]
        if len(candidates) < 4:
            raise ValueError("Each CUTEst panel needs four settings instances")
        problems += sorted(candidates, key=lambda p: digest("tight:" + p["problem"]))[:4]
    return problems


def configurations(base_jobs, problems):
    """Three fixed settings per family; retain the five primary references."""
    by_family = {
        family: next(job for job in base_jobs if job["method"] == family) for family in FAMILIES
    }
    presets = {
        "XR": [("m0=5", {"m0": 5}), ("m0=10", {}), ("m0=20", {"m0": 20})],
        "XR-F": [("m0=5", {"m0": 5}), ("m0=10", {}), ("m0=20", {"m0": 20})],
        "L-BFGS": [("m=5", {"m": 5}), ("m=10", {"m": 10}), ("m=20", {})],
        "L-CG_DESCENT": [("m=5", {"memory": 5}), ("m=11", {}), ("m=20", {"memory": 20})],
        "MS-L-BFGS": [("L8M2", {"m": 8, "M": 2}), ("L8M4", {"m": 8, "M": 4}), ("L8M8", {})],
    }
    expected_primary = {
        "XR": {"m0": 10, "m_max": 100},
        "XR-F": {"m0": 10, "m_max": 100, "values": True},
        "L-BFGS": {"m": 20, "maxls": 20},
        "L-CG_DESCENT": {"memory": 11},
        "MS-L-BFGS": {"m": 8, "M": 8, "exact_last": False},
    }
    result = []
    for family in FAMILIES:
        primary = by_family[family]["params"]
        if any(primary.get(key) != value for key, value in expected_primary[family].items()):
            raise ValueError("Main primary configuration changed: " + family)
        for job in base_jobs:
            if job["method"] == family and job["spec"] in problems:
                if job["params"] != primary:
                    raise ValueError("Nonuniform primary settings in the selected cohort")
                if (job["budget"], job["max_time"], job["relative_gtol"]) != (100000, 120.0, 1e-8):
                    raise ValueError("Main target or budgets differ from the settings protocol")
        for setting, changes in presets[family]:
            result.append(
                dict(
                    id=family + "/" + setting,
                    family=family,
                    setting=setting,
                    params=dict(primary, **changes),
                    primary=not changes,
                )
            )
    return result


def make_manifest(main_folder, *, require_complete=True):
    from xrbench.campaign import digest, environment

    main_folder, base, rows = base_inputs(main_folder, require_complete=require_complete)
    if base["workers"] not in (1, 8) or base["environment"]["blas_threads"] != 1:
        raise ValueError(
            "Settings study requires a supported single-BLAS-thread protocol"
        )
    problems = select_problems(base)
    base_jobs = [
        job for job in base["jobs"] if job["spec"] in problems and job["method"] in FAMILIES
    ]
    if len(base_jobs) != 80:
        raise ValueError("Every selected problem needs all five primary references")
    configs = configurations(base_jobs, problems)
    lookup = {(job["spec"]["problem"], job["method"]): job for job in base_jobs}
    science, script = base["source_hash"], file_hash(SCRIPT)
    jobs, references = [], []
    for config in configs:
        for origin in problems:
            original = lookup[origin["problem"], config["family"]]
            if config["primary"]:
                references.append(
                    dict(
                        configuration=config["id"], job_id=original["id"], problem=origin["problem"]
                    )
                )
                continue
            job = dict(
                spec=dict(origin, suite="settings", origin_suite="cutest"),
                method=config["id"],
                base_method=config["family"],
                label=config["id"],
                params=config["params"],
                budget=100000,
                max_time=120.0,
                relative_gtol=1e-8,
            )
            job["id"] = digest(dict(job=job, source_hash=science, script_sha256=script))[:24]
            jobs.append(job)
    random.Random(20261025).shuffle(jobs)
    return dict(
        version=1,
        stage="settings-sensitivity",
        source_hash=science,
        script_sha256=script,
        base_directory=str(main_folder),
        base_manifest_sha256=file_hash(main_folder / "manifest.json"),
        base_history_sha256=file_hash(main_folder / "history.jsonl") if require_complete else None,
        environment=environment(),
        workers=base["workers"],
        base_workers=base["workers"],
        budget=100000,
        max_time=120.0,
        relative_gtol=1e-8,
        selection="Four per CUTEst panel, SHA256(JSON('tight:'+problem)), matching tolerance supplement",
        timing="Saved wall times are not pooled or ranked across main/settings phases.",
        problems=problems,
        configurations=configs,
        references=references,
        expected_main_rows=len(base["jobs"]),
        completed_main_rows=len(rows),
        jobs=jobs,
    )


def validate_frozen(manifest):
    from xrbench.campaign import source_hash

    if manifest["script_sha256"] != file_hash(SCRIPT):
        raise ValueError("Frozen settings script changed")
    if manifest["source_hash"] != source_hash():
        raise ValueError("Frozen scientific source changed")
    folder = Path(manifest["base_directory"])
    for name, key in (
        ("manifest.json", "base_manifest_sha256"),
        ("history.jsonl", "base_history_sha256"),
    ):
        if not manifest[key] or file_hash(folder / name) != manifest[key]:
            raise ValueError("Frozen main input changed: " + name)
    _, base, rows = base_inputs(folder, require_complete=True)
    return base, rows


def isolated(job):
    from xrbench.campaign import _isolated

    actual = dict(job, method=job["base_method"])
    row = _isolated(actual)
    row.update(
        method=job["method"],
        label=job["label"],
        base_method=job["base_method"],
        relative_gtol=job["relative_gtol"],
        config={"role": "settings"},
    )
    return row


def validate_rows(rows, manifest, *, complete=False):
    jobs = {job["id"]: job for job in manifest["jobs"]}
    present = {row["job_id"] for row in rows}
    if len(present) != len(rows) or present - jobs.keys() or complete and present != jobs.keys():
        raise ValueError("Settings history needs distinct scheduled jobs, including failures")
    for row in rows:
        job = jobs[row["job_id"]]
        if (row.get("source_hash"), row["method"], row["problem"], row["params"]) != (
            manifest["source_hash"],
            job["method"],
            job["spec"]["problem"],
            job["params"],
        ):
            raise ValueError("Settings row disagrees with its frozen source or job")
        if row["success"] != (row["status"] == "converged"):
            raise ValueError("Inconsistent settings success status")
        if row["success"] and not (0 < row["n_g"] < math.inf):
            raise ValueError("A successful settings gradient cost must be positive and finite")


def execute(output, manifest=None):
    from xrbench.campaign import campaign_writer_lock

    with campaign_writer_lock(output):
        return _execute_locked(output, manifest)


def _execute_locked(output, manifest=None):
    from xrbench.campaign import finite, read_history, recover_history_tail

    logs = Path(output) / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    frozen = logs / "manifest.json"
    if frozen.exists():
        if manifest is not None:
            raise ValueError("Frozen settings study exists; use resume")
        manifest = json.loads(frozen.read_text())
    else:
        if manifest is None:
            raise ValueError("New settings execution requires a manifest")
        validate_frozen(manifest)
        frozen.write_text(json.dumps(manifest, indent=2) + "\n")
    validate_frozen(manifest)
    history = logs / "history.jsonl"
    recover_history_tail(history)
    rows = read_history(history)
    validate_rows(rows, manifest)
    done = {row["job_id"] for row in rows}
    jobs = [job for job in manifest["jobs"] if job["id"] not in done]
    print(f"settings: {len(done)}/160 complete, {len(jobs)} pending", flush=True)
    with history.open("a", buffering=1) as stream, (logs / "run.log").open("a", buffering=1) as log:
        with ThreadPoolExecutor(max_workers=manifest["workers"]) as pool:
            for future in as_completed([pool.submit(isolated, job) for job in jobs]):
                row = finite(future.result())
                validate_rows([row], manifest)
                stream.write(dump(row) + "\n")
                stream.flush()
                os.fsync(stream.fileno())
                rows.append(row)
                line = f"{len(rows)}/160 {row['method']} {row['problem']} {row['status']} g={row['n_g']}"
                print(line, flush=True)
                log.write(line + "\n")
                if history.stat().st_size > 32 * 1024 * 1024:
                    raise RuntimeError("Settings history exceeds 32 MiB bound")
    return rows, manifest


def _stats(rows, anchors, problems):
    ratios, only, base_only, neither, solved = [], 0, 0, 0, 0
    for spec in problems:
        current, anchor = rows[spec["problem"]], anchors[spec["problem"]]
        a, b = bool(current["success"]), bool(anchor["success"])
        solved += a
        only += a and not b
        base_only += b and not a
        neither += not a and not b
        if a and b:
            if not (0 < current["n_g"] < math.inf and 0 < anchor["n_g"] < math.inf):
                raise ValueError("Successful reference costs must be positive and finite")
            ratios.append(current["n_g"] / anchor["n_g"])
    return dict(
        solved=solved,
        paired=len(ratios),
        only=only,
        base_only=base_only,
        neither=neither,
        ratio=math.exp(sum(map(math.log, ratios)) / len(ratios)) if ratios else None,
    )


def render(output):
    from xrbench.campaign import read_history
    from xrbench.study import _compact_markdown_tables, _table

    output = Path(output)
    manifest = json.loads((output / "logs" / "manifest.json").read_text())
    _, base_rows = validate_frozen(manifest)
    rows = read_history(output / "logs" / "history.jsonl")
    validate_rows(rows, manifest, complete=True)
    primary = {row["job_id"]: row for row in base_rows}
    grouped = {config["id"]: {} for config in manifest["configurations"]}
    for ref in manifest["references"]:
        grouped[ref["configuration"]][ref["problem"]] = primary[ref["job_id"]]
    for row in rows:
        grouped[row["method"]][row["problem"]] = row
    anchors = {
        config["family"]: grouped[config["id"]]
        for config in manifest["configurations"]
        if config["primary"]
    }
    stats = []
    for config in manifest["configurations"]:
        stats.append(
            dict(
                config,
                **_stats(grouped[config["id"]], anchors[config["family"]], manifest["problems"]),
            )
        )
    table_rows = []
    report = [
        "# Settings sensitivity",
        "",
        "Completed **160/160 new runs**, with **80/80 unchanged main references**; "
        "240 comparison rows on sixteen fixed CUTEst instances.",
        "",
        "Primary presets are retained. All fifteen settings are reported, with no per-problem winner selection. "
        "Each row is compared with its own family's primary configuration, not another solver.",
        "",
        "Budgets: 100000 point-oracle acquisitions and 120 solver seconds; target: "
        f"||g||2 <= 1e-8 max(1,||g0||2). {manifest['workers']} worker(s), one BLAS thread each. "
        "The main isolated worker preserves identical oracle/timing boundaries. Raw wall times are saved, "
        "but no timing ranking combines different campaign phases.",
        "",
        "| Method | Setting | Solved/16 | Paired | Gradient ratio to own base | Variant-only / base-only | Neither |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for row in stats:
        setting = row["setting"] + (" (base)" if row["primary"] else "")
        ratio = f"{row['ratio']:.3f}" if row["ratio"] is not None else "--"
        method = row["family"].replace("_", r"\_")
        table_rows.append(
            [
                method,
                setting,
                f"{row['solved']}/16",
                str(row["paired"]),
                ratio,
                f"{row['only']}/{row['base_only']}",
                str(row["neither"]),
            ]
        )
        report.append(
            f"| {row['family']} | {setting} | {row['solved']}/16 | {row['paired']} | "
            f"{ratio} | {row['only']}/{row['base_only']} | {row['neither']} |"
        )
    tables = output / "tables"
    tables.mkdir(parents=True, exist_ok=True)
    _table(
        tables / "settings_summary.tex",
        "llrrrrr",
        ["Method", "Setting", "Solved", "Pairs", r"$N_g/N_g^{\rm base}$", "$+/-$", "Neither"],
        table_rows,
        r"Fixed-settings sensitivity on sixteen CUTEst instances, four per nonlinear panel. "
        r"XR and XR-F retain memory cap 100; only their initial target memory $m_0$ changes. "
        r"MS-L-BFGS retains eight stored pairs and varies its simultaneous-secant limit. "
        r"Base rows reuse the unchanged main runs. Ratios are geometric means of actual gradient counts "
        r"on common successes; values above one favor that family's base. Exclusive successes $(+/-)$ "
        r"and failures of both settings remain explicit; pairs plus these three counts equal 16.",
        "tab:xr-settings",
    )
    report += [
        "",
        "Ratios omit undefined failure costs only; all failures stay in solved and exclusive-success denominators. "
        "A missing job prevents rendering. This is a sensitivity study, not a new tuned primary solver.",
        "",
        "## Fixed cohort",
        "",
        "Selection: four per panel sorted by SHA256(JSON('tight:'+problem)), "
        "exactly the tighter-target supplement cohort. Development labels are retained; no untouched-holdout claim.",
        "",
    ]
    report += [
        f"- {p['group']}: `{p['problem']}`, n={p['n']}, {p.get('development_role', 'not recorded')}"
        for p in manifest["problems"]
    ]
    report += [
        "",
        "## Source rationale",
        "",
        "L-BFGS 5/10/20 spans a small recommended memory, SciPy's default, "
        "and the fixed primary memory. CG_DESCENT 5/11/20 brackets the native/author default eleven. "
        "MS-L-BFGS L8M2/L8M4/L8M8 are all configurations explicitly tested in Gubarev's Section 5; "
        "sixteen-pair extrapolation is avoided. See `docs/PresetRationale.md` for primary links and limitations.",
        "",
        "## Reproduction",
        "",
        "```sh",
        "python scripts/settings_study.py run --main artifacts/full --output artifacts/settings",
        "python scripts/settings_study.py resume --output artifacts/settings",
        "python scripts/settings_study.py render --output artifacts/settings",
        "```",
        "",
    ]
    for title, key in (
        ("Scientific source", "source_hash"),
        ("Settings script", "script_sha256"),
        ("Main manifest", "base_manifest_sha256"),
        ("Main history", "base_history_sha256"),
    ):
        report += [f"{title} SHA256: `{manifest[key]}`.", ""]
    (output / "REPORT.md").write_text("\n".join(_compact_markdown_tables(report)))
    return dict(runs=len(rows), references=len(manifest["references"]), settings=stats)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "run", "resume", "render"))
    parser.add_argument("--main", type=Path, default=ROOT / "artifacts" / "full")
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts" / "settings")
    args = parser.parse_args()
    if args.action == "plan":
        manifest = make_manifest(args.main, require_complete=False)
        print(
            dump(
                {
                    "jobs": len(manifest["jobs"]),
                    "references": len(manifest["references"]),
                    "source_hash": manifest["source_hash"],
                    "script_sha256": manifest["script_sha256"],
                    "configurations": manifest["configurations"],
                    "problems": manifest["problems"],
                }
            )
        )
        return
    if args.action == "run":
        execute(args.output, make_manifest(args.main))
    elif args.action == "resume":
        execute(args.output)
    print(dump(render(args.output)))


if __name__ == "__main__":
    main()
