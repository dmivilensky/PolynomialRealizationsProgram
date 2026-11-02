"""Pinned supplementary settings, with explicit failures and unchanged anchors."""

import importlib.util
import json
from pathlib import Path

import pytest

from xrbench import campaign


@pytest.fixture
def study(tmp_path, monkeypatch):
    path = Path(__file__).resolve().parents[1] / "scripts" / "settings_study.py"
    spec = importlib.util.spec_from_file_location("settings_study", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    pinned_script = tmp_path / "pinned-script.py"
    pinned_script.write_text("# settings test fixture\n")
    monkeypatch.setattr(module, "SCRIPT", pinned_script)
    monkeypatch.setattr(campaign, "source_hash", lambda: "fixture-science")
    base = campaign.make_manifest()
    base["source_hash"] = "fixture-science"
    cohort = module.select_problems(base)
    base["jobs"] = [
        job for job in base["jobs"] if job["spec"] in cohort and job["method"] in module.FAMILIES
    ]
    folder = tmp_path / "main"
    folder.mkdir()
    (folder / "manifest.json").write_text(json.dumps(base))
    rows = [_row(job) for job in base["jobs"]]
    _write_history(folder / "history.jsonl", rows)
    return module, folder


def _row(job, *, success=True):
    spec = job["spec"]
    return dict(
        job_id=job["id"],
        method=job["method"],
        problem=spec["problem"],
        suite=spec["suite"],
        group=spec["group"],
        n=spec["n"],
        params=job["params"],
        problem_spec=spec,
        source_hash="fixture-science",
        status="converged" if success else "budget",
        success=success,
        n_g=10 if success else 100,
        n_f=12,
        seconds=0.1,
        trace=[],
    )


def _write_history(path, rows):
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))


def test_settings_manifest_has_ten_variants_and_eighty_exact_references(study):
    module, folder = study
    manifest = module.make_manifest(folder)
    assert len(manifest["jobs"]) == 160
    assert len(manifest["references"]) == 80
    assert len(manifest["configurations"]) == 15
    assert sum(config["primary"] for config in manifest["configurations"]) == 5
    assert len({job["id"] for job in manifest["jobs"]}) == 160
    assert manifest["base_history_sha256"] == module.file_hash(folder / "history.jsonl")
    for job in manifest["jobs"]:
        assert (job["budget"], job["max_time"], job["relative_gtol"]) == (100000, 120.0, 1e-8)
        if job["base_method"] in ("XR", "XR-F"):
            assert job["params"]["m0"] in (5, 20)
            assert job["params"]["m_max"] == 100
            assert job["params"]["trial"] == "secant"
            assert job["params"]["floor"] is False
        elif job["base_method"] == "MS-L-BFGS":
            assert job["params"]["m"] == 8
            assert job["params"]["M"] in (2, 4)
            assert job["params"]["exact_last"] is False


def test_settings_uses_exactly_the_existing_tight_hash_cohort(study):
    module, folder = study
    base = json.loads((folder / "manifest.json").read_text())
    selected = module.select_problems(base)
    assert len(selected) == 16
    for group in module.GROUPS:
        candidates = [p for p in base["problems"] if p["suite"] == "cutest" and p["group"] == group]
        expected = sorted(candidates, key=lambda p: campaign.digest("tight:" + p["problem"]))[:4]
        assert [p for p in selected if p["group"] == group] == expected


def test_settings_cannot_start_on_an_incomplete_main(study):
    module, folder = study
    rows = campaign.read_history(folder / "history.jsonl")
    _write_history(folder / "history.jsonl", rows[:-1])
    with pytest.raises(ValueError, match="Complete main"):
        module.make_manifest(folder)
    assert module.make_manifest(folder, require_complete=False)["base_history_sha256"] is None


@pytest.mark.parametrize("changed", ["script", "main-history", "main-manifest", "science"])
def test_settings_refuses_changed_frozen_inputs(study, monkeypatch, changed):
    module, folder = study
    manifest = module.make_manifest(folder)
    if changed == "script":
        module.SCRIPT.write_text("# changed\n")
    elif changed == "science":
        monkeypatch.setattr(campaign, "source_hash", lambda: "changed-science")
    else:
        path = folder / ("history.jsonl" if changed == "main-history" else "manifest.json")
        path.write_text(path.read_text() + "\n")
    with pytest.raises(ValueError, match="changed"):
        module.validate_frozen(manifest)


def test_settings_delegates_to_the_identical_main_worker(study, monkeypatch):
    module, folder = study
    job = module.make_manifest(folder)["jobs"][0]
    calls = []

    def isolate(actual):
        calls.append(actual)
        return _row(actual)

    monkeypatch.setattr(campaign, "_isolated", isolate)
    result = module.isolated(job)
    assert len(calls) == 1
    assert calls[0]["method"] == job["base_method"]
    assert calls[0]["params"] == job["params"]
    assert calls[0]["id"] == job["id"]
    assert result["method"] == job["method"]
    assert result["base_method"] == job["base_method"]
    assert result["n_g"] == 10
    assert result["seconds"] == 0.1


def test_failure_accounting_never_drops_unreached_instances(study):
    module, _ = study
    problems = [dict(problem=name) for name in "abcd"]
    current = {name: dict(success=name in "ac", n_g=2) for name in "abcd"}
    base = {name: dict(success=name in "ab", n_g=1) for name in "abcd"}
    stats = module._stats(current, base, problems)
    assert stats == dict(solved=2, paired=1, only=1, base_only=1, neither=1, ratio=2.0)
    assert stats["paired"] + stats["only"] + stats["base_only"] + stats["neither"] == 4


def test_settings_render_requires_complete_runs_and_keeps_all_failure_rows(study, tmp_path):
    module, folder = study
    manifest = module.make_manifest(folder)
    output = tmp_path / "settings"
    logs = output / "logs"
    logs.mkdir(parents=True)
    (logs / "manifest.json").write_text(json.dumps(manifest))
    rows = [_row(job, success=job["method"] != "L-BFGS/m=5") for job in manifest["jobs"]]
    _write_history(logs / "history.jsonl", rows[:-1])
    with pytest.raises(ValueError, match="scheduled jobs"):
        module.render(output)
    assert not (output / "tables").exists()
    _write_history(logs / "history.jsonl", rows)
    result = module.render(output)
    assert result["runs"] == 160 and result["references"] == 80
    failed = next(row for row in result["settings"] if row["id"] == "L-BFGS/m=5")
    assert failed["solved"] == 0
    assert failed["paired"] == 0 and failed["ratio"] is None
    assert failed["base_only"] == 16
    table = (output / "tables" / "settings_summary.tex").read_text()
    assert r"\label{tab:xr-settings}" in table
    assert "L-BFGS & m=5 & 0/16 & 0 & -- & 16" in table
    assert "Variant only = 0" in table
    assert "Neither" not in table and "$+/-$" not in table
    assert (output / "REPORT.md").is_file()


def test_settings_execution_is_resumable_without_recomputing_saved_jobs(
    study, tmp_path, monkeypatch
):
    module, folder = study
    manifest = module.make_manifest(folder)
    output = tmp_path / "settings"
    calls = []

    def isolate(job):
        calls.append(job["id"])
        return _row(job)

    monkeypatch.setattr(module, "isolated", isolate)
    rows, frozen = module.execute(output, manifest)
    assert len(rows) == len(set(calls)) == 160
    assert frozen["references"] == manifest["references"]
    module.execute(output)
    assert len(calls) == 160
    assert len(campaign.read_history(output / "logs" / "history.jsonl")) == 160
    with pytest.raises(ValueError, match="use resume"):
        module.execute(output, manifest)
