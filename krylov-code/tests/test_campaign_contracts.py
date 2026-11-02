"""Scientific isolation and provenance checks for the replacement runner."""

import json
from copy import deepcopy

import pytest

from xrbench.campaign import (
    ABLATIONS,
    BASELINES,
    PRIMARY,
    _isolated,
    digest,
    execute,
    make_manifest,
    materialize_aliases,
    read_history,
    reuse_cutest_baselines,
    source_hash,
    validate_history,
)


def test_every_primary_solver_receives_exactly_the_same_cutest_instances():
    manifest = make_manifest()
    expected = {p["problem"] for p in manifest["problems"] if p["suite"] == "cutest"}
    assert len(expected) == 257
    for method in PRIMARY:
        actual = {
            j["spec"]["problem"]
            for j in manifest["jobs"]
            if j["method"] == method and j["spec"]["suite"] == "cutest"
        }
        assert actual == expected
    assert len({j["id"] for j in manifest["jobs"]}) == len(manifest["jobs"])


def test_group_boundaries_use_actual_dimensions():
    for spec in make_manifest()["problems"]:
        if spec["group"].endswith("-small"):
            assert spec["n"] <= 300
        if spec["group"].endswith("-large"):
            assert spec["n"] > 300


def test_isolated_backend_budget_counts_initial_gradient_once():
    manifest = make_manifest(budget=1, max_time=10.0, pilot=True)
    job = next(
        j for j in manifest["jobs"] if j["method"] == "L-BFGS" and j["spec"]["suite"] == "quadratic"
    )
    result = _isolated(job)
    assert result["status"] == "budget", result
    assert result["success"] is False
    assert (result["n_g"], result["n_f"], result["n_fg"], result["n_pts"]) == (1, 1, 1, 1)
    assert result["source_hash"] == source_hash()


def test_resume_refuses_changed_computational_source(tmp_path):
    manifest = make_manifest(pilot=True)
    manifest["source_hash"] = "different-source"
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="source/configuration changed"):
        execute(tmp_path)
    assert not (tmp_path / "history.jsonl").exists()


def test_existing_manifest_is_not_overwritten(tmp_path):
    manifest = make_manifest(pilot=True)
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="never overwrite"):
        execute(tmp_path, manifest)


def test_duplicate_results_are_not_silently_reused(tmp_path):
    history = tmp_path / "history.jsonl"
    history.write_text('{"job_id":"same"}\n{"job_id":"same"}\n')
    with pytest.raises(ValueError, match="Duplicate"):
        read_history(history)


def test_ablation_contexts_reuse_identical_primary_observations():
    manifest = make_manifest()
    assert len(manifest["jobs"]) == 2784
    assert len(manifest["aliases"]) == 128
    assert len(manifest["jobs"]) + len(manifest["aliases"]) == 2912
    assert sum(job["spec"]["suite"] == "ablation" for job in manifest["jobs"]) == 320
    jobs = {job["id"]: job for job in manifest["jobs"]}
    for alias in manifest["aliases"]:
        origin = jobs[alias["alias_of"]]
        assert origin["spec"]["suite"] == "cutest"
        assert alias["spec"]["problem"] == "ablation:" + origin["spec"]["problem"]
        assert origin["method"] == ("XR-F" if alias["method"] == "XR-F" else "XR")
    # Both a success and a failure are inherited, without outcome selection.
    aliases = manifest["aliases"][:2]
    rows = [_example_row(jobs[alias["alias_of"]], manifest) for alias in aliases]
    rows[1].update(success=False, status="budget")
    expanded = materialize_aliases(rows, manifest)
    assert len(expanded) == 4
    by_id = {row["job_id"]: row for row in expanded}
    for alias in aliases:
        actual, inherited = by_id[alias["alias_of"]], by_id[alias["id"]]
        for key in ("status", "success", "n_g", "seconds", "trace", "source_hash"):
            assert inherited[key] == actual[key]
        assert inherited["alias_of"] == actual["job_id"]
        assert inherited["suite"] == "ablation"
    with pytest.raises(ValueError, match="materialized alias"):
        materialize_aliases(expanded, manifest)


def test_practical_and_curvature_policy_parameters_are_explicit():
    manifest = make_manifest()
    assert set(ABLATIONS) == {
        "XR-F/F-off",
        "XR-F/fixed-memory",
        "XR-F/positive-only",
        "XR-F/no-probe",
        "XR-F/midpoint-trial",
        "XR-F/lagged-trial",
    }
    for job in manifest["jobs"]:
        if job["method"] in {"XR", "XR-F"}:
            assert job["params"]["trial"] == "secant"
            assert job["params"]["floor"] is False
        elif job["method"] == "XR-F/midpoint-trial":
            assert job["params"]["trial"] == "midpoint"
            assert job["params"]["floor"] is True
        elif job["method"] == "XR-F/lagged-trial":
            assert job["params"]["trial"] == "lagged"
            assert job["params"]["floor"] is False


def test_development_labels_apply_to_whole_cutest_families():
    specs = [spec for spec in make_manifest()["problems"] if "source" in spec]
    for family in ("NCB20B", "PENALTY2", "FREUROTH", "FLETCHCR"):
        family_specs = [spec for spec in specs if spec["source"] == family]
        assert family_specs
        assert {spec["development_role"] for spec in family_specs} == {"development"}
    assert all("holdout" not in spec["development_role"] for spec in specs)


def _example_row(job, manifest):
    spec = job["spec"]
    return dict(
        job_id=job["id"],
        problem=spec["problem"],
        suite=spec["suite"],
        group=spec["group"],
        n=spec["n"],
        method=job["method"],
        label=job["label"],
        params=deepcopy(job["params"]),
        problem_spec=deepcopy(spec),
        source_hash=manifest["source_hash"],
        status="converged",
        success=True,
        n_g=3,
        n_f=5,
        n_fg=2,
        n_pts=4,
        seconds=0.1,
        trace=[{"n_g": 3, "gnorm": 1e-9}],
    )


def _migration_fixture():
    new = make_manifest()
    old = deepcopy(new)
    old["aliases"] = []
    for job in old["jobs"]:
        job["spec"].pop("development_role", None)
        job.pop("id")
        job["id"] = digest(job)[:20]
    chosen = [
        next(
            job
            for job in old["jobs"]
            if job["method"] == method and job["spec"]["suite"] == "cutest"
        )
        for method in BASELINES
    ]
    chosen += [next(job for job in old["jobs"] if job["method"] == "XR")]
    chosen += [
        next(
            job
            for job in old["jobs"]
            if job["method"] == "L-BFGS" and job["spec"]["suite"] == "quadratic"
        )
    ]
    return old, [_example_row(job, old) for job in chosen], new


def test_explicit_migration_reuses_only_unchanged_cutest_baselines():
    old, rows, new = _migration_fixture()
    migrated_manifest, migrated = reuse_cutest_baselines(old, rows, new, producer_maps={})
    assert len(migrated) == 6
    assert {row["method"] for row in migrated} == set(BASELINES)
    assert all(row["suite"] == "cutest" for row in migrated)
    assert all(row["producer_job_id"] != row["job_id"] for row in migrated)
    assert {row["source_hash"] for row in migrated} == {old["source_hash"]}
    assert len(migrated_manifest["baseline_reuse"]["records"]) == 6
    validate_history(migrated, migrated_manifest)


@pytest.mark.parametrize("change", ["oracle", "budget", "target", "parameters", "workers"])
def test_migration_rejects_changed_execution_inputs(change):
    old, rows, new = _migration_fixture()
    if change == "oracle":
        old["source_files"]["src/xrbench/oracle.py"] = "different"
        old["source_hash"] = digest(old["source_files"])
        for row in rows:
            row["source_hash"] = old["source_hash"]
    elif change == "workers":
        new["workers"] += 1
    else:
        key = {"budget": "budget", "target": "relative_gtol", "parameters": "params"}[change]
        for job in new["jobs"]:
            if key == "params":
                job[key]["m"] = 999
            else:
                job[key] *= 2
    with pytest.raises(ValueError, match="changed"):
        reuse_cutest_baselines(old, rows, new, producer_maps={})


def test_history_rejects_undeclared_old_source_even_for_matching_job():
    manifest = make_manifest(pilot=True)
    row = _example_row(manifest["jobs"][0], manifest)
    row["source_hash"] = "an-unverified-producer"
    with pytest.raises(ValueError, match="undeclared producer"):
        validate_history([row], manifest)
