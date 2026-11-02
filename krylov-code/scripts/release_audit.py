#!/usr/bin/env python3
"""Validate the complete expanded native release without launching any solver.

Checks frozen scientific inputs, native build identities, every scheduled job,
actual gradient targets, supplementary script pins, accepted local trajectories
and external LIBSVM arrays. Only logs/audit.json and logs/audit.md are written;
partial or inconsistent releases are refused. Earlier pilot folders are not
counted as final observations, but obey the same output file policy.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import os
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
ALLOWED_EXTENSIONS = {".pdf", ".tex", ".json", ".jsonl", ".md", ".log", ".txt", ".lock"}
COUNTS = {"full": 2976, "settings": 160, "supplement": 289, "local": 120}
TECHNICAL_STATUSES = {"error", "setup_error", "worker_error", "worker_failure", "missing", "running"}


class AuditError(ValueError):
    """An incomplete or inconsistent release cannot receive an audit report."""


def require(condition, message):
    if not condition:
        raise AuditError(message)


def sha(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def load_script(name):
    spec = importlib.util.spec_from_file_location("xr_release_" + name, ROOT / "scripts" / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def complete_jobs(rows, config, expected, label):
    jobs = config["jobs"]
    ids, scheduled = [row["job_id"] for row in rows], [job["id"] for job in jobs]
    require(len(rows) == len(jobs) == expected, f"{label}: expected {expected} complete actual jobs")
    require(len(set(ids)) == len(ids), label + ": duplicate actual job ID")
    require(len(set(scheduled)) == len(scheduled), label + ": duplicate scheduled job ID")
    require(set(ids) == set(scheduled), label + ": actual and scheduled jobs differ")
    return {job["id"]: job for job in jobs}


def validate_observations(rows, jobs, scientific, label):
    for row in rows:
        name = label + ": " + row["problem"] + "/" + row["method"]
        job = jobs[row["job_id"]]
        require(row.get("source_hash") == scientific, name + ": changed producer source")
        require((row["method"], row["problem"], row["suite"], row["params"]) ==
                (job["method"], job["spec"]["problem"], job["spec"]["suite"], job["params"]),
                name + ": observation differs from its scheduled job")
        status = row["status"]
        require(status not in TECHNICAL_STATUSES and not status.startswith("error:"),
                name + ": technical failure " + status)
        require(not row.get("diagnostics") and not row.get("error"), name + ": technical diagnostics")
        require(row["success"] == (status == "converged"), name + ": inconsistent success flag")
        require(row["n_g"] >= row["n_fg"] >= 0 and row["n_f"] >= row["n_fg"],
                name + ": inconsistent actual evaluation counts")
        require(row["n_g"] >= 1 and row["n_pts"] >= 1, name + ": no actual gradient observation")
        require(math.isfinite(row["seconds"]) and row["seconds"] > 0, name + ": invalid measured time")
        initial, target = row.get("initial_gnorm"), row.get("target_gnorm")
        require(initial is not None and math.isfinite(initial) and initial >= 0,
                name + ": invalid first observed gradient")
        expected_target = job["relative_gtol"] * max(1., initial)
        require(target == expected_target, name + ": actual target differs from the frozen rule")
        if row["success"]:
            best = row.get("best_gnorm")
            require(best is not None and math.isfinite(best) and 0 <= best <= target,
                    name + ": successful run did not observe its gradient target")


def outcomes(rows):
    return {method: dict(scheduled=len(selected), solved=sum(r["success"] for r in selected),
                         statuses=dict(sorted(Counter(r["status"] for r in selected).items())))
            for method in sorted({r["method"] for r in rows})
            if (selected := [r for r in rows if r["method"] == method])}


def validate_local(module, config, rows, scientific):
    require(not module.validate(config, rows), "local: missing scheduled observations")
    require(len(rows) == COUNTS["local"], "local: expected 120 actual observations")
    for row in rows:
        name = f"local: {row['method']}, n={row['n']}, kappa={row['kappa']}, seed={row['seed']}"
        require(row["source_hash"] == scientific, name + ": changed producer source")
        require(row.get("backend") == "native-c", name + ": expected native XR execution")
        require(row["success"] == (row["status"] == "converged"), name + ": inconsistent success flag")
        require(row["status"] not in TECHNICAL_STATUSES and not row["status"].startswith("error:"),
                name + ": technical failure")
        trace = row["trace"]
        require(len(trace) == row["accepted"] + 1 and trace[0]["error"] == 1,
                name + ": accepted trajectory is incomplete")
        require([p["iteration"] for p in trace] == list(range(len(trace))), name + ": skipped accepted iterate")
        require([p["n_g"] for p in trace] == sorted(p["n_g"] for p in trace), name + ": nonmonotone oracle clock")
        for point in trace:
            require(point["full_window"] == (point["window_used"] == row["n"]), name + ": false full-window marker")
            require(math.isfinite(point["error"]) and point["error"] >= 0, name + ": invalid analytic error")
            require(math.isfinite(point["gnorm"]) and point["gnorm"] >= 0, name + ": invalid observed gradient")
        actual_full = next((p["n_g"] for p in trace if p["full_window"]), None)
        require(row["first_full_n_g"] == actual_full, name + ": inconsistent first full window")
        require(row["n_g"] >= trace[-1]["n_g"], name + ": impossible terminal oracle clock")
        if row["success"]:
            require(trace[-1]["error"] <= config["target"], name + ": accepted error target was not reached")
    return {method: dict(scheduled=len(selected), solved=sum(r["success"] for r in selected),
                         full_windows=sum(r["first_full_n_g"] is not None for r in selected),
                         statuses=dict(sorted(Counter(r["status"] for r in selected).items())))
            for method in config["methods"]
            if (selected := [r for r in rows if r["method"] == method])}


def audit(base):
    from xrbench.campaign import (
        PRIMARY,
        digest,
        environment,
        make_manifest,
        materialize_aliases,
        read_history,
        source_files,
        source_hash,
        validate_history,
    )
    from xrbench.methods.registry import CATALOG
    from xrbench.native.build import backend_metadata as xr_backend
    from xrbench.native.competitor_build import backend_metadata as competitor_backend
    from xrbench.problems.libsvm import catalog, data_receipts, validate_prepared_data

    scientific = source_hash()
    full = base / "full"
    config = read(full / "manifest.json")
    rows = read_history(full / "history.jsonl")
    require(config["stage"] == "frozen-benchmark", "Expected a final campaign, not a pilot")
    require(config["source_hash"] == scientific and config["source_files"] == source_files(),
            "Main scientific source/configuration changed")
    require(digest(config["source_files"]) == scientific, "Invalid frozen source map")
    require(not config.get("baseline_reuse"), "Final release must contain fresh measured baseline runs")
    require(config["workers"] == 1 and config["environment"]["blas_threads"] == 1,
            "Main timing must be sequential with one BLAS thread")
    require(config["environment"] == environment(), "Current scientific environment changed")
    require(config["budget"] == 100000 and config["max_time"] == 120 and config["libsvm_max_time"] == 300,
            "Main resource limits changed")
    planned = make_manifest(workers=1, include_libsvm=True)
    require(config["jobs"] == planned["jobs"] and config["aliases"] == planned["aliases"],
            "Final scheduled jobs differ from the current frozen protocol")
    jobs = complete_jobs(rows, config, COUNTS["full"], "full")
    validate_history(rows, config)
    validate_observations(rows, jobs, scientific, "full")
    require(len(config["aliases"]) == 128, "Expected 128 explicit main aliases")
    comparisons = materialize_aliases(rows, config)
    require(len(comparisons) == COUNTS["full"] + 128, "Alias materialization count changed")
    require(sum(bool(r.get("alias_of")) for r in comparisons) == 128, "Invalid alias lineage")

    require(set(config["implementations"]) == set(PRIMARY), "Missing primary implementation provenance")
    expected_modules = {"XR": "xr_native", "XR-F": "xr_native", "L-BFGS": "lbfgs_scipy",
                        "L-CG_DESCENT": "cgdescent", **{m: "competitors_native" for m in PRIMARY[4:]}}
    for method, module in expected_modules.items():
        require(CATALOG[method]["module"] == "xrbench.methods." + module,
                "Expected compiled primary implementation: " + method)
    current_builds = {"native_backend": xr_backend(), "competitor_native_backend": competitor_backend()}
    for key, metadata in current_builds.items():
        require(config[key] == metadata, "Frozen native build changed: " + key)
    for filename, checksum in config["formal_reference"]["files"].items():
        require(sha(ROOT.parent / filename) == checksum, "Frozen mathematical reference changed: " + filename)

    require(config["libsvm_data"] == data_receipts(), "Current LIBSVM receipts changed")
    require(len(config["libsvm_data"]) == len(catalog()["datasets"]) == 8, "Expected eight external datasets")
    validate_prepared_data(config["libsvm_data"])
    lib_jobs = [j for j in config["jobs"] if j["spec"]["suite"] == "libsvm"]
    lib_rows = [r for r in rows if r["suite"] == "libsvm"]
    require(len(lib_jobs) == len(lib_rows) == 192, "Expected 24 LIBSVM objectives by eight methods")
    lib_contexts = Counter(j["spec"]["problem"] for j in lib_jobs)
    require(len(lib_contexts) == 24 and set(lib_contexts.values()) == {8}, "Incomplete LIBSVM common cohort")
    for context in lib_contexts:
        selected = [j for j in lib_jobs if j["spec"]["problem"] == context]
        require({j["method"] for j in selected} == set(PRIMARY),
                "LIBSVM context does not contain every primary method: " + context)
    for job in lib_jobs:
        require(job["max_time"] == 300 and job["relative_gtol"] == 1e-8, "LIBSVM target or time limit changed")
    for method in PRIMARY:
        require(sum(r["suite"] == "cutest" and r["method"] == method for r in rows) == 257,
                "Incomplete CUTEst cohort for " + method)
        require(sum(r["method"] == method for r in lib_rows) == 24, "Incomplete LIBSVM cohort for " + method)

    paths = {"full": (full / "manifest.json", full / "history.jsonl")}
    phases = {"full": dict(actual=len(rows), aliases=128, statuses=dict(Counter(r["status"] for r in rows)))}
    for name, script_name in (("settings", "settings_study"), ("supplement", "supplement")):
        folder = base / name / "logs"
        extra = read(folder / "manifest.json")
        records = read_history(folder / "history.jsonl")
        module = load_script(script_name)
        module.validate_frozen(extra)
        require(extra["source_hash"] == scientific and extra["workers"] == 1,
                name + ": source or sequential workload changed")
        require(Path(extra["base_directory"]).resolve() == full.resolve(), name + ": wrong main release referenced")
        scheduled = complete_jobs(records, extra, COUNTS[name], name)
        validate_observations(records, scheduled, scientific, name)
        if name == "settings":
            module.validate_rows(records, extra, complete=True)
            require(len(extra["references"]) == 80, "Expected 80 settings primary references")
        phases[name] = dict(actual=len(records), references=80 if name == "settings" else 0,
                            statuses=dict(Counter(r["status"] for r in records)))
        paths[name] = (folder / "manifest.json", folder / "history.jsonl")

    local_folder = base / "local/logs"
    local_config = read(local_folder / "manifest.json")
    local_rows = read_history_local(local_folder / "history.jsonl")
    local_outcomes = validate_local(load_script("local_study"), local_config, local_rows, scientific)
    phases["local"] = dict(actual=len(local_rows), outcomes=local_outcomes)
    paths["local"] = (local_folder / "manifest.json", local_folder / "history.jsonl")
    require(sum(phase["actual"] for phase in phases.values()) == 3545, "Expected 3545 actual final computations")

    unexpected, bytes_by_extension = [], Counter()
    for path in base.rglob("*"):
        if path.is_file():
            if path.suffix not in ALLOWED_EXTENSIONS:
                unexpected.append(str(path.relative_to(base)))
            if path.name not in {"audit.json", "audit.md"}:
                bytes_by_extension[path.suffix] += path.stat().st_size
    require(not unexpected, "Unexpected release outputs: " + ", ".join(unexpected))
    require(source_hash() == scientific, "Scientific source changed during audit")
    return dict(schema="xr-native-expanded-release-audit-v1", status="complete",
                source_hash=scientific, actual_runs=3545, main_aliases=128, settings_references=80,
                phases=phases, cutest=outcomes([r for r in rows if r["suite"] == "cutest"]),
                libsvm=outcomes(lib_rows), libsvm_contexts=24, libsvm_datasets=8,
                data_receipts=config["libsvm_data"], implementations=config["implementations"],
                builds=current_builds,
                files={name: {"manifest_sha256": sha(manifest), "history_sha256": sha(history)}
                       for name, (manifest, history) in paths.items()},
                scripts={name: sha(ROOT / "scripts" / (name + ".py"))
                         for name in ("release_audit", "settings_study", "supplement", "local_study")},
                output_policy=dict(allowed_extensions=sorted(ALLOWED_EXTENSIONS),
                                   bytes_by_extension=dict(sorted(bytes_by_extension.items())),
                                   scope="Expanded release only, including historical pilot logs; audit outputs excluded from byte totals"))


def read_history_local(path):
    # Local observations have a Cartesian-product identity rather than job_id;
    # local_study.validate checks uniqueness and completeness of that identity.
    return [json.loads(line) for line in Path(path).read_text().splitlines()]


def markdown(result):
    lines = ["# Expanded native release audit", "", "Status: **complete**.", "",
             f"Scientific source SHA256: `{result['source_hash']}`.", "",
             "All 3545 actual final computations are present. Main aliases (128) and settings references (80) are counted separately.",
             "No solver was launched by this audit. Frozen scripts, native builds, data arrays and actual targets were checked.", "",
             "| Series | Actual runs |", "|---|---:|"]
    lines += [f"| {name} | {phase['actual']} |" for name, phase in result["phases"].items()]
    lines += ["", "| Method | CUTEst solved / 257 | LIBSVM solved / 24 |", "|---|---:|---:|"]
    lines += [f"| {method} | {stats['solved']} | {result['libsvm'][method]['solved']} |"
              for method, stats in result["cutest"].items()]
    lines += ["", "The local audit verifies every accepted iterate, analytic error target and full-window marker.",
              "Only vector PDFs, TeX tables and scalar logs/reports occur inside the expanded release.",
              "Per-series file hashes, outcomes, implementation provenance and native build identities are in `audit.json`.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "artifacts/run")
    args = parser.parse_args()
    for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
                 "VECLIB_MAXIMUM_THREADS", "BLIS_NUM_THREADS"):
        os.environ[name] = "1"
    base = args.output.resolve()
    try:
        result = audit(base)
    except (ValueError, KeyError, OSError) as ex:
        parser.exit(1, "Release audit refused: " + str(ex) + "\n")
    logs = base / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    for filename, contents in (("audit.json", json.dumps(result, indent=2, sort_keys=True, allow_nan=False) + "\n"),
                               ("audit.md", markdown(result))):
        temporary = logs / (filename + ".tmp")
        temporary.write_text(contents)
        temporary.replace(logs / filename)
    print("Expanded release audit complete: 3545 actual runs; reports in", logs)


if __name__ == "__main__":
    main()
