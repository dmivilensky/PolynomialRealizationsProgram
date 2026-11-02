#!/usr/bin/env python3
"""Frozen supplementary BFGS and tighter-target studies; never modify main results.

Run only after the main campaign completes. The main scientific source hash,
base manifest/history and this script are pinned. The extra BFGS registration
exists only inside each isolated worker; the primary eight-method registry is
unchanged. Output consists of bounded JSON/JSONL logs, two native TeX tables,
and a Markdown report. Rendering never evaluates an objective.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from copy import deepcopy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = Path(__file__).resolve()
sys.path.insert(0, str(ROOT / "src"))
GROUPS = ("sos-small", "sos-large", "general-small", "general-large")
BFGS = "BFGS-SP"


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def base_inputs(folder, *, require_complete):
    from xrbench.campaign import read_history, source_hash, validate_history

    folder = Path(folder).resolve()
    manifest_path, history_path = folder / "manifest.json", folder / "history.jsonl"
    manifest = json.loads(manifest_path.read_text())
    if manifest["source_hash"] != source_hash():
        raise ValueError("Main campaign source/configuration changed")
    rows = read_history(history_path)
    validate_history(rows, manifest)
    scheduled = {job["id"] for job in manifest["jobs"]}
    present = {row["job_id"] for row in rows}
    if present - scheduled or require_complete and present != scheduled:
        raise ValueError("Main campaign must be complete before supplementary execution")
    return folder, manifest, rows


def make_manifest(main_folder, workers=8, *, require_complete=True):
    from xrbench.campaign import LABELS, PRIMARY, digest, environment

    if workers not in (1, 4, 8):
        raise ValueError("workers must be explicitly 1, 4 or 8")
    main_folder, base, rows = base_inputs(main_folder, require_complete=require_complete)
    scientific_hash, script_sha = base["source_hash"], file_hash(SCRIPT)
    problems = base["problems"]
    reference = [p for p in problems if p["suite"] == "cutest" and p["n"] <= 300]
    reference += [p for p in problems if p["suite"] == "quadratic"]
    if len([p for p in reference if p["suite"] == "quadratic"]) != 12:
        raise ValueError("Expected the frozen twelve synthetic quadratic instances")
    tight = []
    for group in GROUPS:
        candidates = [p for p in problems if p["suite"] == "cutest" and p["group"] == group]
        if len(candidates) < 4:
            raise ValueError("Every tight-target group needs at least four instances")
        tight += sorted(candidates, key=lambda p: digest("tight:" + p["problem"]))[:4]
    lookup = {(j["spec"]["suite"], j["spec"]["problem"], j["method"]): j for j in base["jobs"]}
    jobs = []
    for origin in reference:
        spec = dict(origin, origin_suite=origin["suite"], suite="bfgs-reference")
        jobs.append(dict(spec=spec, method=BFGS, label=BFGS, params={}, budget=100000,
                         max_time=120., relative_gtol=1e-8))
    for origin in tight:
        for method in PRIMARY:
            job = deepcopy(lookup["cutest", origin["problem"], method])
            job.pop("id", None)
            job.update(spec=dict(origin, origin_suite="cutest", suite="tolerance"),
                       label=LABELS[method], budget=100000, max_time=120., relative_gtol=1e-10)
            jobs.append(job)
    for job in jobs:
        job["id"] = digest(dict(job=job, source_hash=scientific_hash, script_sha256=script_sha))[:24]
    random.Random(20261024).shuffle(jobs)
    return dict(version=1, stage="supplementary", source_hash=scientific_hash,
                script_sha256=script_sha, base_directory=str(main_folder),
                base_manifest_sha256=file_hash(main_folder / "manifest.json"),
                base_history_sha256=file_hash(main_folder / "history.jsonl") if require_complete else None,
                workers=workers, base_workers=base["workers"], environment=environment(),
                selection="SHA256(JSON('tight:'+problem)); four per fixed nonquadratic CUTEst group",
                timing="Actual per-run wall times saved; gradient comparisons use complete common cohorts.",
                budget=100000, max_time=120.,
                target="BFGS: 1e-8 max(1,||g0||2); tolerance: 1e-10 max(1,||g0||2)",
                bfgs_problems=reference, tolerance_problems=tight,
                expected_main_rows=len(base["jobs"]), completed_main_rows=len(rows), jobs=jobs)


def worker(job):
    from xrbench.campaign import run_job
    from xrbench.methods.registry import METHODS

    if job["method"] == BFGS:
        METHODS[BFGS] = ("xrbench.methods.bfgs_sp", {}, "reference", {"max_n": 300})
    result = run_job(job)
    result["relative_gtol"] = job["relative_gtol"]
    result["origin_suite"] = job["spec"]["origin_suite"]
    result["config"]["role"] = "reference" if job["method"] == BFGS else "tolerance"
    return result


def isolated(job):
    env = dict(os.environ, PYTHONPATH=str(ROOT / "src"), PYTHONDONTWRITEBYTECODE="1")
    for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
                 "VECLIB_MAXIMUM_THREADS", "BLIS_NUM_THREADS"):
        env[name] = "1"
    start = time.perf_counter()
    try:
        run = subprocess.run([sys.executable, "-B", str(SCRIPT), "--worker"], input=dump(job),
                             capture_output=True, text=True, env=env, timeout=job["max_time"] + 120)
        output = [line.removeprefix("XR_RESULT ") for line in run.stdout.splitlines()
                  if line.startswith("XR_RESULT ")]
        if output:
            row = json.loads(output[-1])
            if run.stderr:
                row["diagnostics"] = run.stderr[-2000:]
            return row
        reason = f"worker exit {run.returncode}: {run.stderr[-2000:]}"
    except subprocess.TimeoutExpired:
        reason = "external watchdog exceeded scientific budget + 120s startup/grace"
    spec = job["spec"]
    return dict(problem=spec["problem"], suite=spec["suite"], origin_suite=spec["origin_suite"],
                group=spec["group"], n=spec["n"], method=job["method"], label=job["label"],
                params=job["params"], job_id=job["id"], status="worker_failure", success=False,
                n_g=0, n_f=0, n_fg=0, n_pts=0, seconds=time.perf_counter() - start,
                relative_gtol=job["relative_gtol"], error=reason, trace=[])


def validate_frozen(manifest):
    from xrbench.campaign import source_hash

    if manifest["script_sha256"] != file_hash(SCRIPT):
        raise ValueError("Frozen supplementary script changed")
    folder, base, rows = base_inputs(manifest["base_directory"], require_complete=True)
    if manifest["source_hash"] != source_hash():
        raise ValueError("Frozen scientific source changed")
    for name, key in (("manifest.json", "base_manifest_sha256"), ("history.jsonl", "base_history_sha256")):
        if file_hash(folder / name) != manifest[key]:
            raise ValueError("Frozen main input changed: " + name)
    return base, rows


def execute(output, manifest=None):
    from xrbench.campaign import campaign_writer_lock

    with campaign_writer_lock(output):
        return _execute_locked(output, manifest)


def _execute_locked(output, manifest=None):
    from xrbench.campaign import finite, read_history, recover_history_tail

    output = Path(output)
    logs = output / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    frozen = logs / "manifest.json"
    if frozen.exists():
        if manifest is not None:
            raise ValueError("Frozen supplement exists; use resume")
        manifest = json.loads(frozen.read_text())
    else:
        if manifest is None:
            raise ValueError("Missing supplementary manifest")
        validate_frozen(manifest)
        frozen.write_text(json.dumps(manifest, indent=2) + "\n")
    validate_frozen(manifest)
    history_path = logs / "history.jsonl"
    recover_history_tail(history_path)
    rows = read_history(history_path)
    scheduled = {job["id"] for job in manifest["jobs"]}
    if {row["job_id"] for row in rows} - scheduled:
        raise ValueError("Unknown supplementary job ID")
    done = {row["job_id"] for row in rows}
    pending = [job for job in manifest["jobs"] if job["id"] not in done]
    print(f"supplement: {len(done)}/{len(scheduled)} complete, {len(pending)} pending", flush=True)
    with history_path.open("a", buffering=1) as stream, (logs / "run.log").open("a", buffering=1) as log:
        with ThreadPoolExecutor(max_workers=manifest["workers"]) as pool:
            futures = [pool.submit(isolated, job) for job in pending]
            for result in as_completed(futures):
                row = result.result()
                stream.write(dump(finite(row)) + "\n")
                stream.flush()
                os.fsync(stream.fileno())
                rows.append(row)
                line = (f"{len(rows)}/{len(scheduled)} {row['suite']} {row['method']} "
                        f"{row['problem']} {row['status']} g={row['n_g']} t={row['seconds']:.4g}")
                print(line, flush=True)
                log.write(line + "\n")
                if history_path.stat().st_size > 32 * 1024 * 1024:
                    raise RuntimeError("Supplementary history exceeds 32 MiB bound")
    return rows, manifest


def _geomean(values):
    return math.exp(sum(math.log(value) for value in values) / len(values)) if values else None


def _ratio(a, b):
    if a and b and a.get("success") and b.get("success") and a["n_g"] > 0 and b["n_g"] > 0:
        return a["n_g"] / b["n_g"]
    return None


def _label(text):
    return text.replace("_", r"\_")


def render(output):
    from xrbench.campaign import LABELS, PRIMARY, read_history
    from xrbench.study import _compact_markdown_tables, _table

    output = Path(output)
    manifest = json.loads((output / "logs" / "manifest.json").read_text())
    _, base_rows = validate_frozen(manifest)
    rows = read_history(output / "logs" / "history.jsonl")
    if {row["job_id"] for row in rows} != {job["id"] for job in manifest["jobs"]}:
        raise ValueError("Supplementary tables require every scheduled job, including failures")
    tables = output / "tables"
    tables.mkdir(parents=True, exist_ok=True)
    base = {(row["suite"], row["problem"], row["method"]): row for row in base_rows}
    extra = {(row["suite"], row["problem"], row["method"]): row for row in rows}
    reference = manifest["bfgs_problems"]
    counts = {suite: sum(p["suite"] == suite for p in reference) for suite in ("cutest", "quadratic")}
    reference_stats = []
    table_rows = []
    for method in [*PRIMARY, BFGS]:
        solved = dict(cutest=0, quadratic=0)
        ratios, xr_only, method_only = [], 0, 0
        for spec in reference:
            anchor = base[spec["suite"], spec["problem"], "XR"]
            current = extra["bfgs-reference", spec["problem"], BFGS] if method == BFGS else base[spec["suite"], spec["problem"], method]
            solved[spec["suite"]] += bool(current["success"])
            ratio = _ratio(current, anchor)
            if ratio is not None:
                ratios.append(ratio)
            xr_only += bool(anchor["success"] and not current["success"])
            method_only += bool(current["success"] and not anchor["success"])
        factor = _geomean(ratios)
        cells = [_label(LABELS.get(method, method)), f"{solved['cutest']}/{counts['cutest']}",
                 f"{solved['quadratic']}/{counts['quadratic']}", f"{factor:.2f}" if factor else "--",
                 str(len(ratios)), f"{xr_only}/{method_only}"]
        table_rows.append(cells)
        reference_stats.append(dict(method=method, solved=solved, paired=len(ratios), gradient_ratio=factor,
                                    xr_only=xr_only, method_only=method_only))
    _table(
        tables / "bfgs_reference.tex", "lrrrrr",
        ["Method", "CUTEst", "Quadratics", r"$N_g/N_g^{\rm XR}$", "Pairs", "XR only / other only"],
        table_rows,
        r"Supplementary full-memory BFGS-SP reference. Every method uses the same complete small-CUTEst and twelve-quadratic cohort and the $10^{-8}$ relative gradient target. Gradient ratios are geometric means only on common successes; exclusive-success counts remain explicit. BFGS-SP is additional to the primary eight methods.",
        "tab:bfgs-reference",
    )
    tight_stats = []
    table_rows = []
    for method in PRIMARY:
        loose, tight, ratios = 0, 0, []
        grouped = {group: 0 for group in GROUPS}
        for spec in manifest["tolerance_problems"]:
            original = base["cutest", spec["problem"], method]
            current = extra["tolerance", spec["problem"], method]
            loose += bool(original["success"])
            tight += bool(current["success"])
            grouped[spec["group"]] += bool(current["success"])
            ratio = _ratio(current, original)
            if ratio is not None:
                ratios.append(ratio)
        factor = _geomean(ratios)
        cells = [_label(LABELS[method]), f"{loose}/16", f"{tight}/16", f"{factor:.2f}" if factor else "--", str(len(ratios))]
        table_rows.append(cells)
        tight_stats.append(dict(method=method, loose_solved=loose, tight_solved=tight, gradient_ratio=factor,
                               paired=len(ratios), tight_solved_by_group=grouped))
    _table(
        tables / "tighter_target.tex", "lrrrr",
        ["Method", r"Solved at $10^{-8}$", r"Solved at $10^{-10}$", r"$N_g^{10}/N_g^8$", "Paired"],
        table_rows,
        "Tighter-target sensitivity on sixteen outcome-independent CUTEst instances, four from each primary group, selected by the frozen hash rule. Every tighter-target entry is an actual new run with the same method parameters, 100000-point budget and 120-second limit. Ratios compare paired successful runs; failed instances remain in the solved-count denominators.",
        "tab:tighter-target",
    )
    failures = [r for r in rows if not r["success"]]
    lines = ["# Supplementary experiment report", "", f"Completed **{len(rows)}/{len(rows)}** frozen supplementary runs.", "",
             f"BFGS-SP: {counts['cutest']} small CUTEst instances and {counts['quadratic']} quadratics. "
             "Tighter target: 16 hash-selected CUTEst instances × 8 primary methods.", "",
             "The main eight-method results are read from their original immutable history; no main result is overwritten. "
             "The BFGS registration exists only in an isolated supplementary worker. The point and time budgets are 100000 and 120 seconds.", "",
             f"Supplementary workers: {manifest['workers']}; main workers: {manifest['base_workers']}. "
             "Both phases cap BLAS threads at one and exclude problem setup and module imports from solver timing. "
             "The tables compare gradient costs; raw wall times remain in the history, without pooling distinct campaign phases into a speed claim.", "",
             "## BFGS reference", "", "| Method | CUTEst solved | Quadratics solved | Paired gradient ratio to XR | XR-only / method-only |", "| --- | ---: | ---: | ---: | ---: |"]
    for row in reference_stats:
        factor = row["gradient_ratio"]
        cost = f"{factor:.3g} ({row['paired']} pairs)" if factor is not None else "-- (0 pairs)"
        lines.append(f"| {LABELS.get(row['method'],row['method'])} | {row['solved']['cutest']}/{counts['cutest']} | "
                     f"{row['solved']['quadratic']}/{counts['quadratic']} | {cost} | {row['xr_only']}/{row['method_only']} |")
    lines += ["", "## Tighter target", "", "| Method | Solved 1e-8 | Solved 1e-10 | Paired gradient increase |", "| --- | ---: | ---: | ---: |"]
    for row in tight_stats:
        factor = row["gradient_ratio"]
        value = f"{factor:.3g} ({row['paired']} pairs)" if factor is not None else "--"
        lines.append(f"| {LABELS[row['method']]} | {row['loose_solved']}/16 | {row['tight_solved']}/16 | {value} |")
    lines += ["", f"Failures or budget/time stops: **{len(failures)}**. These remain failed, without relaxed targets or replacement costs.", "",
              "Selection uses only frozen problem identifiers; results do not choose the cohort. "
              "A tighter-target stop is a numerical/practical limitation, not a contradiction of an exact-real theorem.", "",
              "## Reproduction", "", "```sh", "python scripts/supplement.py run --main artifacts/full --output artifacts/supplement --workers 8", "python scripts/supplement.py resume --output artifacts/supplement", "python scripts/supplement.py render --output artifacts/supplement", "```", "",
              f"Scientific source SHA256: `{manifest['source_hash']}`.", "",
              f"Script SHA256: `{manifest['script_sha256']}`.", "",
              f"Main manifest SHA256: `{manifest['base_manifest_sha256']}`.", "",
              f"Main history SHA256: `{manifest['base_history_sha256']}`."]
    (output / "REPORT.md").write_text("\n".join(_compact_markdown_tables(lines)) + "\n")
    return dict(runs=len(rows), failures=len(failures), bfgs=reference_stats, tolerance=tight_stats)


def main():
    if sys.argv[1:] == ["--worker"]:
        print("XR_RESULT " + dump(worker(json.load(sys.stdin))), flush=True)
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "run", "resume", "render"))
    parser.add_argument("--main", type=Path, default=ROOT / "artifacts" / "full")
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts" / "supplement")
    parser.add_argument("--workers", type=int, choices=(1, 4, 8), default=8)
    args = parser.parse_args()
    if args.action == "plan":
        manifest = make_manifest(args.main, args.workers, require_complete=False)
        print(dump({"source_hash": manifest["source_hash"], "script_sha256": manifest["script_sha256"],
                    "bfgs_runs": len(manifest["bfgs_problems"]), "tighter_target_runs": 128,
                    "jobs": len(manifest["jobs"]), "workers": manifest["workers"],
                    "tolerance_cohort": [p["problem"] for p in manifest["tolerance_problems"]]}))
        return
    if args.action == "run":
        manifest = make_manifest(args.main, args.workers)
        execute(args.output, manifest)
    elif args.action == "resume":
        execute(args.output)
    print(dump(render(args.output)))


if __name__ == "__main__":
    main()
