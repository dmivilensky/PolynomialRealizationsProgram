"""Frozen studies and isolated processes; only bounded JSONL history is saved."""

import hashlib
import importlib.metadata
import json
import os
import random
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from copy import deepcopy
from pathlib import Path

from xrbench.paths import ROOT

PRIMARY = ["XR", "XR-F", "L-BFGS", "L-CG_DESCENT", "MS-L-BFGS", "SC-MSS", "L-SR1", "O-ACCEL"]
LABELS = dict(
    zip(
        PRIMARY,
        [
            "XR",
            "XR-F",
            "L-BFGS(20)",
            "L-CG_DESCENT(11)",
            "MS-L-BFGS(8,8)",
            "SC-MSS(3,5)",
            "SC-SR1(5,7)",
            "O-ACCEL-B",
        ],
    )
)
ABLATIONS = [
    "XR-F/" + k
    for k in [
        "F-off",
        "fixed-memory",
        "positive-only",
        "no-probe",
        "midpoint-trial",
        "lagged-trial",
    ]
]
BASELINES = [method for method in PRIMARY if method not in {"XR", "XR-F"}]
DEVELOPMENT_FAMILIES = {"NCB20B", "PENALTY2", "FREUROTH", "FLETCHCR"}

# A baseline may be migrated only when its entire mathematical call path is
# unchanged. Registry entries and scheduling code are checked semantically;
# paths only locate the same pinned external native installation.
_SHARED_DEPENDENCIES = [
    "src/xrbench/oracle.py",
    "src/xrbench/protocol.py",
    "src/xrbench/problems/cutest.py",
    "src/xrbench/problems/cutest.json",
    "src/xrbench/methods/registry.py",
]
_BASELINE_DEPENDENCIES = {
    "L-BFGS": ["lbfgs_scipy.py"],
    "L-CG_DESCENT": ["cgdescent.py"],
    "MS-L-BFGS": ["mslbfgs.py"],
    "SC-MSS": ["lmss.py", "_trust_region.py"],
    "L-SR1": ["lsr1.py", "lmss.py", "_trust_region.py"],
    "O-ACCEL": ["oaccel.py"],
}


def finite(v):
    if isinstance(v, dict):
        return {str(k): finite(x) for k, x in v.items()}
    if isinstance(v, (list, tuple)):
        return [finite(x) for x in v]
    if hasattr(v, "item"):
        return finite(v.item())
    if isinstance(v, float) and not (-float("inf") < v < float("inf")):
        return None
    return v


def digest(v):
    return hashlib.sha256(json.dumps(v, sort_keys=True).encode()).hexdigest()


def source_files():
    files = [p for p in sorted((ROOT / "src").rglob("*.py")) if p.name not in {"study.py"}]
    files += sorted((ROOT / "src").rglob("*.json"))
    # The native executor is part of the scientific implementation. Never
    # resume a frozen campaign after a C source/header change.
    files += sorted((ROOT / "src").rglob("*.c"))
    files += sorted((ROOT / "src").rglob("*.h"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def source_hash():
    return digest(source_files())


def environment():
    versions = {}
    for name in ["numpy", "scipy", "pycgdescent", "pycutest", "matplotlib"]:
        try:
            versions[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            versions[name] = "not installed"
    return dict(python=sys.version, platform=sys.platform, versions=versions, blas_threads=1)


def freeze_implementation_metadata(manifest):
    """Compile once before measurements and pin the actual loaded programs."""
    from xrbench.native.build import backend_metadata as xr_metadata
    from xrbench.native.competitor_build import backend_metadata as competitor_metadata

    manifest["native_backend"] = xr_metadata()
    manifest["competitor_native_backend"] = competitor_metadata()
    manifest["implementations"] = {
        "XR": "Our C executor; SciPy BLAS/LAPACK capsules",
        "XR-F": "Our C executor; SciPy BLAS/LAPACK capsules",
        "L-BFGS": "SciPy compiled L-BFGS-B 3.0 descendant, unconstrained",
        "L-CG_DESCENT": "Author CG_DESCENT 6.8 C through pycgdescent",
        "MS-L-BFGS": "Our source-audited full C implementation of published uniform L8M8",
        "SC-MSS": "Our full C port audited against author SC-INF-D source",
        "L-SR1": "Our full C port audited against author Algorithm 1030 SC-INF/Init.2 source",
        "O-ACCEL": "Our full C port audited against author O-ACCEL-B source",
    }
    proof_paths = [ROOT.parent / "krylov/XR/Practical.lean",
                   ROOT.parent / "krylov/XR/PracticalQuadratic.lean"]
    manifest["formal_reference"] = dict(
        scope="Exact-real practical secant policy; floating-point executors are independently tested",
        files={str(p.relative_to(ROOT.parent)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in proof_paths})
    if "libsvm" in manifest["methods"]:
        from xrbench.problems.libsvm import data_receipts

        manifest["libsvm_data"] = data_receipts()
    return manifest


def problem_specs():
    from xrbench.problems.cutest import load_list

    out = []
    for r in load_list():
        name = (
            r["name"]
            + "["
            + ",".join(f"{k}={v}" for k, v in sorted((r["sif"] or {}).items()))
            + "]"
        )
        typ = {"sum of squares": "sos", "other": "general", "quadratic": "quadratic"}[
            r["objective"]
        ]
        group = typ + ("-small" if r["n"] <= 300 else "-large") if typ != "quadratic" else typ
        out.append(
            dict(
                problem=name,
                suite="cutest",
                group=group,
                n=r["n"],
                source=r["name"],
                sif=r["sif"],
                objective=r["objective"],
            )
        )
    for suite, ns, ks, es, seeds in [
        ("quadratic", [20, 100], [1e2, 1e4], [0.0], [0, 1, 2]),
        ("perturbed", [100], [1e2, 1e3, 1e4], [1e-3, 0.1, 1.0, 10.0], [0, 1, 2]),
        ("local", [3, 5, 10], [10.0, 100.0], [0.1], [0, 1]),
    ]:
        for n in ns:
            for k in ks:
                for e in es:
                    for seed in seeds:
                        out.append(
                            dict(
                                problem=f"{suite}-n{n}-k{k:g}-e{e:g}-s{seed}",
                                suite=suite,
                                group=suite,
                                n=n,
                                kappa=k,
                                epsilon=e,
                                seed=seed,
                            )
                        )
    for group in ["sos-small", "sos-large", "general-small", "general-large"]:
        candidates = [r for r in out if r["suite"] == "cutest" and r["group"] == group]
        for r in sorted(candidates, key=lambda r: digest(r["problem"]))[:16]:
            out.append(dict(r, suite="ablation", problem="ablation:" + r["problem"]))
    # Families used to develop the practical rule and the original pilot are
    # disclosed. The remaining cohort is a benchmark, not a statistical holdout:
    # earlier listing-based runs had already touched many of these instances.
    pilot_families = set()
    for group in ["sos-small", "sos-large", "general-small", "general-large"]:
        candidates = [s for s in out if s["suite"] == "cutest" and s["group"] == group]
        pilot_families.update(
            s["source"]
            for s in sorted(candidates, key=lambda s: digest("pilot:" + s["problem"]))[:2]
        )
    for spec in out:
        if "source" in spec:
            spec["development_role"] = (
                "development"
                if spec["source"] in DEVELOPMENT_FAMILIES
                else "pilot-diagnostic"
                if spec["source"] in pilot_families
                else "remaining-benchmark"
            )
    return out


def make_problem(s):
    if s["suite"] == "libsvm":
        from xrbench.problems.libsvm import LogisticProblem, receipt_hash

        if receipt_hash(s["dataset"]) != s["data_receipt_sha256"]:
            raise ValueError("Frozen LIBSVM data receipt changed")
        return LogisticProblem(s["dataset"], s["regularization"])
    if "source" in s:
        from xrbench.problems.cutest import make

        return make(s["source"], s.get("sif"))
    from xrbench.problems.synthetic import SmoothQuadratic

    return SmoothQuadratic(s["n"], s["kappa"], s["epsilon"], s["seed"], local=s["suite"] == "local")


def libsvm_specs():
    from xrbench.problems.libsvm import catalog, data_receipts, receipt_hash

    data_receipts()
    return [dict(problem=f"libsvm:{s['name']}:lambda={reg:g}", suite="libsvm",
                 group=s["group"], n=s["features"] + 1, samples=s["rows"],
                 dataset=s["name"], regularization=reg,
                 data_receipt_sha256=receipt_hash(s["name"]))
            for s in catalog()["datasets"] for reg in catalog()["regularization"]]


def make_manifest(budget=100000, max_time=120.0, workers=8, pilot=False, *,
                  include_libsvm=False, libsvm_time=300.0):
    from xrbench.methods.registry import CATALOG

    specs = problem_specs()
    methods = {
        "cutest": PRIMARY,
        "quadratic": PRIMARY,
        "perturbed": PRIMARY,
        "local": ["XR", "XR-F"],
        "ablation": ["XR-F"] + ABLATIONS,
    }
    if include_libsvm:
        specs += libsvm_specs()
        methods["libsvm"] = PRIMARY
    if pilot:
        chosen = []
        for group in ["sos-small", "sos-large", "general-small", "general-large"]:
            chosen += sorted(
                [s for s in specs if s["suite"] == "cutest" and s["group"] == group],
                key=lambda s: digest("pilot:" + s["problem"]),
            )[:2]
        for suite in ["quadratic", "perturbed", "local"]:
            chosen += [s for s in specs if s["suite"] == suite][:2]
        if include_libsvm:
            for group in ("moderate", "many-samples", "dense-highdim", "sparse-highdim"):
                chosen += [s for s in specs if s["suite"] == "libsvm" and s["group"] == group][:1]
        specs = chosen
    jobs, aliases = [], []
    for s in specs:
        for method in methods[s["suite"]]:
            params = dict(CATALOG[method]["params"])
            if s["suite"] == "local":
                params.update(m0=s["n"], m_max=s["n"])
            j = dict(
                spec=s,
                method=method,
                label=LABELS.get(method, method),
                params=params,
                budget=budget,
                max_time=libsvm_time if s["suite"] == "libsvm" else max_time,
                relative_gtol=1e-13 if s["suite"] == "local" else 1e-8,
            )
            j["id"] = digest(j)[:20]
            jobs.append(j)
    primary_jobs = {
        (j["spec"]["problem"], j["method"]): j for j in jobs if j["spec"]["suite"] == "cutest"
    }
    for job in jobs:
        if job["spec"]["suite"] == "ablation" and job["method"] in {"XR-F", "XR-F/F-off"}:
            source_method = "XR-F" if job["method"] == "XR-F" else "XR"
            source = primary_jobs[job["spec"]["problem"].removeprefix("ablation:"), source_method]
            # Explicit values=False and its default denote the same algorithm.
            if dict(job["params"], values=job["params"].get("values", False)) != dict(
                source["params"], values=source["params"].get("values", False)
            ):
                raise ValueError("Ablation alias has different algorithm parameters")
            aliases.append(dict(job, alias_of=source["id"]))
    alias_ids = {j["id"] for j in aliases}
    jobs = [j for j in jobs if j["id"] not in alias_ids]
    random.Random(20261023).shuffle(jobs)
    files = source_files()
    return dict(
        version=2,
        created=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        stage="pilot" if pilot else "frozen-benchmark",
        source_hash=digest(files),
        source_files=files,
        environment=environment(),
        budget=budget,
        max_time=max_time,
        workers=workers,
        libsvm_max_time=libsvm_time if include_libsvm else None,
        timing="Sequential isolated solvers, one BLAS thread" if workers == 1 else "Concurrent isolated solvers, one BLAS thread each",
        target="||g||2 <= 1e-8 max(1,||g0||2); local diagnostic 1e-13",
        protocol="separate-f-g-cache4-v3",
        cohort_policy={
            "development_families": sorted(DEVELOPMENT_FAMILIES),
            "pilot": "Two SHA256-selected instances per nonquadratic CUTEst group; family-level labels.",
            "remaining": "Remaining benchmark families; no independent held-out validation claim.",
        },
        problems=specs,
        methods=methods,
        jobs=jobs,
        aliases=aliases,
    )


def run_job(j):
    import numpy as np

    from xrbench.methods.registry import get_solve
    from xrbench.oracle import run_method

    s = j["spec"]
    row = dict(
        problem=s["problem"],
        source_hash=source_hash(),
        suite=s["suite"],
        group=s["group"],
        n=s["n"],
        method=j["method"],
        label=j["label"],
        job_id=j["id"],
        params=j["params"],
        problem_spec=s,
        config=dict(role="ablation" if s["suite"] == "ablation" else "practical"),
    )
    setup_start = time.perf_counter()
    try:
        p = make_problem(s)
        # Equal module warm-up: SR1 delegates its initial search to MSS,
        # which would otherwise import scipy.optimize inside only its timer.
        # No solver is run and no problem information is acquired here.
        for name in PRIMARY:
            get_solve(name)
        solver = get_solve(j["method"])
        # Native modules/BLAS capsule setup are loaded outside every solver's
        # timer. The common warm-up performs no objective evaluation.
        from xrbench.native.competitor_build import load_native as load_competitors

        load_competitors()
        setup_seconds = time.perf_counter() - setup_start
        with np.errstate(over="ignore", under="ignore", invalid="ignore", divide="ignore"):
            r = run_method(
                solver,
                p,
                p.x0,
                j["params"],
                budget=j["budget"],
                max_time=j["max_time"],
                relative_gtol=j["relative_gtol"],
            )
        row.update(
            status=r["status"],
            success=r["status"] == "converged",
            n_g=r["n_g_evals"],
            n_f=r["n_f_evals"],
            n_fg=r["n_fg_evals"],
            n_pts=r["n_pts"],
            n_it=r["n_it"],
            seconds=r["time"],
            cpu_seconds=r["cpu_time"],
            setup_seconds=setup_seconds,
            best_gnorm=r["best_gn"],
            initial_gnorm=r["initial_gnorm"],
            target_gnorm=r["target_gnorm"],
            best_f=r["best_f"],
            trace=r["trace"],
            milestones=r["milestones"],
            info=r["info"],
        )
    except Exception as ex:
        row.update(
            status="setup_error",
            success=False,
            n_g=0,
            n_f=0,
            n_fg=0,
            n_pts=0,
            seconds=0.0,
            setup_seconds=time.perf_counter() - setup_start,
            error=type(ex).__name__ + ": " + str(ex)[:1000],
            trace=[],
        )
    return finite(row)


def _isolated(j):
    env = dict(os.environ, PYTHONPATH=str(ROOT / "src"), PYTHONDONTWRITEBYTECODE="1")
    for key in [
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
        "BLIS_NUM_THREADS",
    ]:
        env[key] = "1"
    start = time.perf_counter()
    try:
        p = subprocess.run(
            [sys.executable, "-B", "-m", "xrbench", "_worker"],
            input=json.dumps(j),
            capture_output=True,
            text=True,
            env=env,
            timeout=j["max_time"] + 120,
        )
        rows = [l[len("XR_RESULT ") :] for l in p.stdout.splitlines() if l.startswith("XR_RESULT ")]
        if rows:
            row = json.loads(rows[-1])
            if p.stderr:
                row["diagnostics"] = p.stderr[-2000:]
            return row
        reason = f"worker exit {p.returncode}: " + p.stderr[-2000:]
    except subprocess.TimeoutExpired:
        reason = "external watchdog exceeded scientific budget + 120s startup/grace"
    s = j["spec"]
    return dict(
        problem=s["problem"],
        source_hash=source_hash(),
        suite=s["suite"],
        group=s["group"],
        n=s["n"],
        method=j["method"],
        label=j["label"],
        job_id=j["id"],
        params=j["params"],
        status="worker_failure",
        success=False,
        n_g=0,
        n_f=0,
        n_fg=0,
        n_pts=0,
        seconds=time.perf_counter() - start,
        error=reason,
        trace=[],
    )


def read_history(path):
    p = Path(path)
    rows = [json.loads(l) for l in p.read_text().splitlines()] if p.exists() else []
    if len({r["job_id"] for r in rows}) != len(rows):
        raise ValueError("Duplicate saved job IDs")
    return rows


def recover_history_tail(path):
    """Repair only an interrupted final append, preserving its bytes in a log.

    Completed records are never discarded. A valid JSON final record merely
    needs its missing newline; a partial record has no completed observation
    and that job is recomputed on resume. Earlier corruption remains an error.
    Call only while holding the campaign writer lock.
    """
    path = Path(path)
    if not path.exists():
        return
    raw = path.read_bytes()
    if not raw or raw.endswith(b"\n"):
        return
    boundary = raw.rfind(b"\n") + 1
    for line in raw[:boundary].splitlines():
        json.loads(line)
    try:
        json.loads(raw[boundary:])
    except (ValueError, UnicodeDecodeError):
        logs = path.parent / "logs"
        logs.mkdir(exist_ok=True)
        saved = logs / f"interrupted-tail-{time.time_ns()}.log"
        saved.write_bytes(raw[boundary:])
        with path.open("r+b") as stream:
            stream.truncate(boundary)
        print("Recovered interrupted history tail; bytes preserved in", saved, flush=True)
    else:
        with path.open("ab") as stream:
            stream.write(b"\n")


def materialize_aliases(records, manifest):
    """Add declared comparison contexts without creating new observations.

    Only actual computations belong in history.jsonl. An ablation reusing the
    identical primary run inherits every measurement, including failures and
    its complete trace. The context and explicit alias_of field are the only
    changes; no result is selected or recomputed here.
    """
    rows = [deepcopy(row) for row in records]
    by_id = {row["job_id"]: row for row in rows}
    if len(by_id) != len(rows):
        raise ValueError("Duplicate saved job IDs")
    scheduled = {job["id"] for job in manifest["jobs"]}
    if set(by_id) - scheduled:
        raise ValueError("History contains an unscheduled or materialized alias job")
    for alias in manifest.get("aliases", []):
        source = by_id.get(alias["alias_of"])
        if source is None:
            continue
        row = deepcopy(source)
        spec = alias["spec"]
        row.update(
            job_id=alias["id"],
            alias_of=alias["alias_of"],
            problem=spec["problem"],
            suite=spec["suite"],
            group=spec["group"],
            n=spec["n"],
            method=alias["method"],
            label=alias["label"],
            params=alias["params"],
            problem_spec=spec,
            config={"role": "ablation"},
        )
        if row["job_id"] in by_id:
            raise ValueError("Duplicate alias job ID")
        by_id[row["job_id"]] = row
        rows.append(row)
    return rows


def _baseline_signature(job):
    """Execution inputs, excluding presentation-only cohort annotations."""
    spec = job["spec"]
    return digest(
        {
            "method": job["method"],
            "params": job["params"],
            "budget": job["budget"],
            "max_time": job["max_time"],
            "relative_gtol": job["relative_gtol"],
            "spec": {
                key: spec.get(key)
                for key in ("suite", "problem", "source", "sif", "n", "objective", "group")
            },
        }
    )


def reuse_cutest_baselines(previous, records, manifest, *, producer_maps):
    """Explicitly migrate unchanged CUTEst baselines, with a checkable lineage.

    The caller supplies source-file maps for every producer revision. Synthetic
    runs and all XR runs are always excluded. Equality is checked on algorithm
    dependencies, the oracle, native adaptor, data list, effective registered
    arguments, stopping limits, thread counts, package versions and worker load.
    This never runs automatically when a campaign is resumed.
    """
    for key in ("protocol", "environment", "workers"):
        if previous[key] != manifest[key]:
            raise ValueError("Baseline reuse changed execution setting: " + key)
    if digest(previous["source_files"]) != previous["source_hash"]:
        raise ValueError("Previous manifest source-file map is invalid")
    if digest(manifest["source_files"]) != manifest["source_hash"]:
        raise ValueError("New manifest source-file map is invalid")
    maps = dict(producer_maps)
    maps[previous["source_hash"]] = previous["source_files"]
    for revision, files in maps.items():
        if digest(files) != revision:
            raise ValueError("Producer source-file map is invalid: " + revision)
    old_jobs = {job["id"]: job for job in previous["jobs"]}
    new_jobs = {
        _baseline_signature(job): job
        for job in manifest["jobs"]
        if job["spec"]["suite"] == "cutest" and job["method"] in BASELINES
    }
    if len({row["job_id"] for row in records}) != len(records):
        raise ValueError("Duplicate previous results")
    migrated, lineage, checked = [], [], {}
    used = set()
    for row in records:
        if row["suite"] != "cutest" or row["method"] not in BASELINES:
            continue
        old = old_jobs.get(row["job_id"])
        if old is None:
            raise ValueError("Previous baseline job is absent from its manifest")
        if row["params"] != old["params"] or row["problem_spec"] != old["spec"]:
            raise ValueError("Previous baseline row disagrees with its manifest")
        job = new_jobs.get(_baseline_signature(old))
        if job is None:
            raise ValueError("Baseline reuse changed problem, arguments, budget or target")
        producer = row.get("source_hash")
        if producer not in maps:
            raise ValueError("Missing explicit producer source-file map: " + str(producer))
        dependencies = _SHARED_DEPENDENCIES + [
            "src/xrbench/methods/" + name for name in _BASELINE_DEPENDENCIES[row["method"]]
        ]
        if row["method"] in {"MS-L-BFGS", "SC-MSS", "L-SR1", "O-ACCEL"}:
            dependencies += ["src/xrbench/methods/competitors_native.py"]
            dependencies += ["src/xrbench/native/" + name for name in
                             ("competitor_build.py", "build.py", "competitor_common.c",
                              "competitor_common.h", "competitor_bridge.c", "xr_native.h")]
            port_files = {
                "MS-L-BFGS": ["mslbfgs_native.c", "mslbfgs_native.h"],
                "SC-MSS": ["sc_native.c", "sc_native.h"],
                "L-SR1": ["sc_native.c", "sc_native.h"],
                "O-ACCEL": ["oaccel_native.c"],
            }
            dependencies += ["src/xrbench/native/" + name for name in port_files[row["method"]]]
        for path in dependencies:
            if maps[producer].get(path) != manifest["source_files"].get(path):
                raise ValueError("Baseline reuse changed dependency: " + path)
        checked.setdefault(producer, {})[row["method"]] = dependencies
        if job["id"] in used:
            raise ValueError("Multiple previous observations map to one new job")
        used.add(job["id"])
        migrated_row = deepcopy(row)
        migrated_row.update(
            job_id=job["id"],
            producer_job_id=row["job_id"],
            reused_unchanged_cutest_baseline=True,
            problem_spec=job["spec"],
        )
        migrated.append(migrated_row)
        lineage.append(
            {
                "job_id": job["id"],
                "producer_job_id": row["job_id"],
                "producer_source_hash": producer,
            }
        )
    result = deepcopy(manifest)
    result["revisions"] = deepcopy(previous.get("revisions", []))
    result["baseline_reuse"] = {
        "prior_source_hash": previous["source_hash"],
        "policy": "Only six unchanged CUTEst baselines; all XR and synthetic runs discarded.",
        "semantic_checks": [
            "problem/SIF/dimension/objective/group",
            "method parameters",
            "gradient target",
            "gradient budget",
            "time budget",
            "single-thread kernels",
            "package versions",
            "parallel worker load",
        ],
        "dependency_checks": checked,
        "producer_source_files": {revision: maps[revision] for revision in checked},
        "records": lineage,
    }
    return result, migrated


def validate_history(records, manifest):
    """Reject extra jobs and undeclared provenance before resuming or reporting."""
    jobs = {job["id"]: job for job in manifest["jobs"]}
    inherited = {
        row["job_id"]: row for row in manifest.get("baseline_reuse", {}).get("records", [])
    }
    for row in records:
        job = jobs.get(row["job_id"])
        if job is None:
            raise ValueError("History contains an unscheduled job")
        if (row["method"], row["problem"], row["suite"], row["params"]) != (
            job["method"],
            job["spec"]["problem"],
            job["spec"]["suite"],
            job["params"],
        ):
            raise ValueError("History row disagrees with the frozen job")
        if row.get("source_hash") != manifest["source_hash"]:
            origin = inherited.get(row["job_id"], {})
            if (origin.get("producer_source_hash"), origin.get("producer_job_id")) != (
                row.get("source_hash"),
                row.get("producer_job_id"),
            ) or not origin:
                raise ValueError("History contains undeclared producer provenance")


@contextmanager
def campaign_writer_lock(folder):
    """Every entry point protects the append boundary, including direct CLI."""
    import fcntl

    logs = Path(folder) / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    with (logs / "writer.lock").open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError("Another process owns the campaign writer lock") from error
        yield


def execute(folder, manifest=None):
    with campaign_writer_lock(folder):
        return _execute_locked(folder, manifest)


def _execute_locked(folder, manifest=None):
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    mp = folder / "manifest.json"
    if mp.exists():
        if manifest is not None:
            raise ValueError("Use resume; never overwrite frozen protocol")
        manifest = json.loads(mp.read_text())
    else:
        if manifest is None:
            raise ValueError("New campaign requires a manifest")
        mp.write_text(json.dumps(manifest, indent=2) + "\n")
    if manifest["source_hash"] != source_hash():
        raise ValueError("Frozen source/configuration changed")
    if manifest.get("libsvm_data"):
        from xrbench.problems.libsvm import validate_prepared_data

        validate_prepared_data(manifest["libsvm_data"])
    if manifest.get("native_backend"):
        from xrbench.native.build import backend_metadata as xr_backend_metadata

        if xr_backend_metadata() != manifest["native_backend"]:
            raise ValueError("Frozen native XR build changed")
    if manifest.get("competitor_native_backend"):
        from xrbench.native.competitor_build import backend_metadata

        if backend_metadata() != manifest["competitor_native_backend"]:
            raise ValueError("Frozen native competitor build changed")
    hp = folder / "history.jsonl"
    recover_history_tail(hp)
    records = read_history(hp)
    validate_history(records, manifest)
    done = {r["job_id"] for r in records}
    jobs = [j for j in manifest["jobs"] if j["id"] not in done]
    print(
        f"{manifest['stage']}: {len(done)}/{len(manifest['jobs'])} saved, {len(jobs)} pending",
        flush=True,
    )
    with hp.open("a", buffering=1) as history, (folder / "run.log").open("a", buffering=1) as log:
        with ThreadPoolExecutor(max_workers=manifest["workers"]) as pool:
            futures = [pool.submit(_isolated, j) for j in jobs]
            for f in as_completed(futures):
                row = f.result()
                history.write(
                    json.dumps(finite(row), separators=(",", ":"), allow_nan=False) + "\n"
                )
                history.flush()
                os.fsync(history.fileno())
                records.append(row)
                text = (
                    f"{len(records)}/{len(manifest['jobs'])} {row['suite']} {row['method']} "
                    f"{row['problem']} {row['status']} g={row['n_g']} t={row['seconds']:.4g}"
                )
                log.write(text + "\n")
                print(text, flush=True)
                if hp.stat().st_size > 128 * 1024 * 1024:
                    raise RuntimeError("History exceeds 128 MiB limit")
    return materialize_aliases(records, manifest), manifest
