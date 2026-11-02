"""Statistical contracts for failure-aware profiles and compact artifacts."""

import hashlib
import importlib.util
import json
import math
from pathlib import Path

import pytest

from xrbench.study import (
    _compact_markdown_tables,
    _development_sensitivity,
    _family_sensitivity,
    _local_accuracy_statistics,
    _native_campaign_provenance,
    _native_provenance,
    _perturbed_grid,
    _publication_table,
    _shared_full_pair_count,
    _table,
    conditional_logit_profile,
    conditional_logit_ticks,
    performance_profiles,
    profile_view_ranges,
    render,
    render_local_study,
)


def row(problem, method, cost, *, success=True, suite="cutest", group="sos-small"):
    return {
        "problem": problem,
        "method": method,
        "label": method,
        "suite": suite,
        "group": group,
        "n": 100,
        "success": success,
        "status": "success" if success else "budget",
        "n_g": cost,
        "n_f": cost,
        "n_fg": 0,
        "n_pts": cost,
        "seconds": cost / 10,
    }


def test_profiles_keep_all_failures_and_exact_ties():
    records = [
        row("tie", "XR", 2),
        row("tie", "XR-F", 2),
        row("different", "XR", 4),
        row("different", "XR-F", 2),
        row("failed", "XR", 10, success=False),
        row("failed", "XR-F", 10, success=False),
    ]
    result = performance_profiles(records, ["XR", "XR-F"], ["tie", "different", "failed"])
    assert result["x"] == [1, 2]
    assert result["ratios"]["XR"] == [1, 2, math.inf]
    assert result["curves"]["XR"] == [1 / 3, 2 / 3]
    assert result["curves"]["XR-F"] == [2 / 3, 2 / 3]
    assert result["all_failed"] == ["failed"]
    assert result["missing"] == []


def local_config(*, seeds=(0, 1, 2, 3), methods=("XR",)):
    return dict(
        dimensions=[10],
        condition_numbers=[100],
        seeds=list(seeds),
        methods=list(methods),
        epsilon=0.1,
        initial_base_energy=0.03,
        target=1e-12,
    )


def local_row(seed, method="XR", *, errors=(1.0, 1e-6, 1e-13), success=True):
    return dict(
        method=method,
        n=10,
        kappa=100,
        seed=seed,
        success=success,
        status="converged" if success else "budget",
        n_g=11,
        n_f=15,
        first_full_n_g=11,
        trace=[
            dict(
                iteration=i,
                n_g=1 + 5 * i,
                error=error,
                full_window=i == 2,
                counters={"nsafe": int(i == 1)},
            )
            for i, error in enumerate(errors)
        ],
    )


def test_local_quantiles_keep_missing_and_unattained_contexts_at_infinity():
    rows = [
        local_row(0),
        local_row(1, errors=(1, 1e-3), success=False),
        local_row(2, errors=(1, 1e-1), success=False),
    ]
    result = _local_accuracy_statistics(rows, local_config())
    assert result["missing"] == 1
    first = result["statistics"]["XR"][0]
    assert first == dict(digit=2, q25=0.6, median=0.6, q75=math.inf, attained=2, n=4)
    last = result["statistics"]["XR"][-1]
    assert last["attained"] == 1 and last["median"] == math.inf
    assert last["q25"] == 1.1
    # Late rejected/budgeted queries cannot replace a missing accepted hit.
    assert rows[1]["n_g"] == 11 and first["median"] < rows[1]["n_g"] / 10


def test_local_study_rejects_missing_accepted_points_and_duplicate_cases():
    config = local_config(seeds=(0,))
    invalid = local_row(0)
    invalid["trace"][1]["iteration"] = 2
    with pytest.raises(ValueError, match="every accepted iterate"):
        _local_accuracy_statistics([invalid], config)
    with pytest.raises(ValueError, match="Duplicate"):
        _local_accuracy_statistics([local_row(0)] * 2, config)
    invalid = local_row(0)
    invalid["trace"] = []
    with pytest.raises(ValueError, match="every accepted iterate"):
        _local_accuracy_statistics([invalid], config)
    invalid = local_row(0)
    invalid["trace"][-1]["n_g"] = 2
    with pytest.raises(ValueError, match="chronological"):
        _local_accuracy_statistics([invalid], config)
    invalid = local_row(0)
    invalid["accepted"] = 4
    with pytest.raises(ValueError, match="accepted count"):
        _local_accuracy_statistics([invalid], config)


def test_dense_local_renderer_keeps_actual_points_and_separate_artifacts(tmp_path):
    config = local_config(seeds=(0, 1), methods=("XR", "XR-F"))
    config["dimensions"] = [5, 20]
    rows = []
    for n in config["dimensions"]:
        for seed in config["seeds"]:
            for method in config["methods"]:
                rows.append(dict(local_row(seed, method), n=n))
    result = render_local_study(rows, tmp_path, config)
    assert result["complete"] and result["contexts"] == 4
    assert (tmp_path / "figures/local.pdf").read_bytes().startswith(b"%PDF")
    assert {p.suffix for p in tmp_path.rglob("*") if p.is_file()} == {".pdf", ".tex", ".md"}
    report = (tmp_path / "REPORT.md").read_text()
    assert "including the initial point" in report
    assert "Rejected probes cannot satisfy" in report
    assert "without smoothing" in report
    assert "R-order estimation" in report
    assert "Renderer SHA-256" in report
    table = (tmp_path / "tables/local_summary.tex").read_text()
    assert "All 8 runs reach the target and use a full window" in table
    assert "Target =" not in table and "Full window =" not in table
    assert len(result["trajectories"]) == 4
    assert {case["n"] for case in result["trajectories"]} == {5, 20}
    assert all(case["accepted_points"] == 3 for case in result["trajectories"])
    assert all(case["first_full_iteration"] == 2 for case in result["trajectories"])
    assert "actual iteration k" in report and "both axes use the same scales" in report


def test_overview_and_logit_keep_full_tail_and_disclose_conditional_denominator():
    records = [
        row("p", "XR", 1),
        row("p", "L-BFGS", 1_000_000),
        row("q", "XR", 2, success=False),
        row("q", "L-BFGS", 2, success=False),
    ]
    profile = performance_profiles(records, ["XR", "L-BFGS"], ["p", "q"])
    views = profile_view_ranges(profile)
    assert views["full_xlim"][1] >= 1_000_000
    assert views["logit_xlim"] == views["full_xlim"]
    assert views["full_ylim"][0] == 0
    assert profile["curves"]["XR"][-1] == profile["curves"]["L-BFGS"][-1] == 0.5
    conditional = conditional_logit_profile(profile)
    assert conditional["n"] == conditional["excluded"] == 1
    assert conditional["curves"]["XR"] == [math.log(3), math.log(3)]
    assert conditional["curves"]["L-BFGS"] == [-math.log(3), math.log(3)]
    renamed = performance_profiles(records, ["L-BFGS", "XR"], ["p", "q"])
    assert profile_view_ranges(renamed) == views


def test_conditional_logit_retains_individual_failures_and_handles_no_success():
    records = [
        row("one", "XR", 1),
        row("one", "L-BFGS", 1, success=False),
        row("both", "XR", 1),
        row("both", "L-BFGS", 1),
        row("none", "XR", 1, success=False),
        row("none", "L-BFGS", 1, success=False),
    ]
    profile = performance_profiles(records, ["XR", "L-BFGS"], ["one", "both", "none"])
    transformed = conditional_logit_profile(profile)
    assert transformed["n"] == 2 and transformed["excluded"] == 1
    assert transformed["counts"] == {"XR": [2], "L-BFGS": [1]}
    assert transformed["curves"]["XR"] == [math.log(5)]
    assert transformed["curves"]["L-BFGS"] == [0]
    empty = conditional_logit_profile(performance_profiles(records, ["XR", "L-BFGS"], ["none"]))
    assert empty["n"] == 0 and all(math.isnan(v[0]) for v in empty["curves"].values())


def test_conditional_percentage_ticks_are_exact_and_leave_room_near_one():
    assert conditional_logit_ticks(0) == ([], [])
    assert conditional_logit_ticks(1)[1] == ["0%", "50%", "100%"]
    for n in (43, 61, 67, 77):
        values, labels = conditional_logit_ticks(n)
        assert labels == ["0%", "50%", "90%", "100%"]
        assert values[0] == -math.log(2 * n + 1)
        assert values[-1] == math.log(2 * n + 1)
        assert values[2] == math.log((n * 0.9 + 0.5) / (n * 0.1 + 0.5))
    assert conditional_logit_ticks(1000)[1] == ["0%", "50%", "90%", "99%", "100%"]


def test_constant_table_columns_move_exact_counts_including_failures_to_caption(tmp_path):
    path = tmp_path / "table.tex"
    _table(
        path,
        "lrrr",
        ["Method", "Solved", "Paired", "Cost"],
        [["XR", "19/20", "18", "1"], ["XR-F", "19/20", "18", "2"]],
        "No runs excluded.",
        "tab:example",
    )
    table = path.read_text()
    assert "Method & Cost" in table
    assert "XR & 1" in table and "XR-F & 2" in table
    assert "Solved = 19/20; Both solved = 18" in table


def test_settings_publication_headers_define_exclusives_and_ratio_direction():
    columns, header, rows, caption = _publication_table(
        "llrrrrr",
        ["Method", "Setting", "Solved", "Pairs", r"$N_g/N_g^{\rm base}$", "$+/-$", "Neither"],
        [["XR", "m0=5", "14/16", "12", "1.1", "2/1", "1"]],
        "Original pinned-script caption.",
        "tab:xr-settings",
    )
    assert columns == "llrrrrr"
    assert header[-2:] == ["Variant only", "Base only"]
    assert header[3] == "Both solved" and "variant" in header[4] and "base" in header[4]
    assert "Neither" not in header and "$+/-$" not in header
    assert rows[0][-2:] == ["2", "1"]
    assert "exclusive successes" in caption


def test_markdown_compacts_counts_without_hiding_common_failures_or_cohort_labels():
    source = [
        "| Suite | Method | Solved | Missing | Mean Ng |",
        "|---|---|---:|---:|---:|",
        "| cutest | XR | 19/20 | 0 | 2 |",
        "| cutest | XR-F | 19/20 | 0 | 2 |",
    ]
    text = "\n".join(_compact_markdown_tables(source))
    assert "| Suite | Method | Mean Ng |" in text
    assert "| cutest | XR | 2 |" in text
    assert "Solved = 19/20; Missing = 0" in text
    # One missing run changes the data, so that column must remain visible.
    source[-1] = "| cutest | XR-F | 18/20 | 1 | 2 |"
    text = "\n".join(_compact_markdown_tables(source))
    assert "| Suite | Method | Solved | Missing | Mean Ng |" in text
    assert "Common across this table" not in text


def test_native_provenance_separates_measured_pilot_and_nonlinear_rounding(tmp_path):
    pilot = tmp_path / "pilot.json"
    pilot.write_text(
        json.dumps(
            dict(
                source_hash="native-science",
                protocol="three alternating serial repeats",
                cases=[dict(speedup=2.32), dict(speedup=6.92)],
            )
        )
    )
    manifest = dict(
        source_hash="native-science",
        native_backend=dict(
            compiler_version="clang fixture",
            flags=["-O3", "-fno-fast-math"],
            build_key="build",
            extension_sha256="extension",
        ),
        hardware=dict(processor="Apple M4 Max", cpu_cores=14, memory_gb=36),
        native_port_pilot=dict(report=str(pilot), policy="Measured anew"),
    )
    text = "\n".join(_native_provenance(manifest, tmp_path))
    assert "14 CPU cores" in text and "36 GB" in text
    assert "frozen C executor" in text and "-fno-fast-math" in text
    assert "from 2.32 to 6.92" in text
    assert "no bitwise-equivalence claim" in text
    assert "no pilot time rescales" in text
    assert "same scientific fingerprint" in text
    manifest["source_hash"] = "later-science"
    assert "historical scientific fingerprint" in "\n".join(_native_provenance(manifest, tmp_path))


def test_full_native_comparison_requires_exact_current_manifest_and_history(tmp_path):
    manifest = dict(source_hash="current")
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    (tmp_path / "history.jsonl").write_text("fixture history\n")
    comparison = dict(
        native=dict(
            source_hash="current",
            manifest_sha256=hashlib.sha256((tmp_path / "manifest.json").read_bytes()).hexdigest(),
            history_sha256=hashlib.sha256((tmp_path / "history.jsonl").read_bytes()).hexdigest(),
        ),
        methods={
            "XR": dict(
                jointly_successful=234,
                total=257,
                python_over_native_wall_geomean=2.89,
                python_over_native_gradients_geomean=1.022,
                native_only=["a", "b", "c"],
                python_only=["d"],
            )
        },
    )
    path = tmp_path / "comparison.json"
    path.write_text(json.dumps(comparison))
    text = "\n".join(_native_campaign_provenance(manifest, tmp_path, path))
    assert "| XR | 234/257 | 2.89 | 1.022 | 3 | 1 |" in text
    assert "no bitwise or identical-outcomes claim" in text
    assert "separate concurrent phases" in text
    (tmp_path / "history.jsonl").write_text("changed history\n")
    assert _native_campaign_provenance(manifest, tmp_path, path) == []


def test_supplement_compacts_common_counts_and_reports_zero_joint_failures(tmp_path, monkeypatch):
    from xrbench import campaign

    script = Path(__file__).resolve().parents[1] / "scripts/supplement.py"
    spec = importlib.util.spec_from_file_location("supplement_render_test", script)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    problems = [dict(problem=f"p{i}", suite="cutest", group="sos-small") for i in range(16)]
    reference = [problems[0], dict(problem="q", suite="quadratic")]
    base = [
        row(p["problem"], method, 2, suite=p["suite"])
        for p in [*problems, reference[1]]
        for method in campaign.PRIMARY
    ]
    extra = [
        dict(row(p["problem"], method, 2, suite="tolerance"), job_id=f"{method}-{i}")
        for i, p in enumerate(problems)
        for method in campaign.PRIMARY
    ]
    extra += [
        dict(row(p["problem"], module.BFGS, 2, suite="bfgs-reference"), job_id=f"bfgs-{i}")
        for i, p in enumerate(reference)
    ]
    logs = tmp_path / "logs"
    logs.mkdir()
    manifest = dict(
        jobs=[dict(id=r["job_id"]) for r in extra],
        bfgs_problems=reference,
        tolerance_problems=problems,
        workers=8,
        base_workers=8,
        source_hash="fixture",
        script_sha256="fixture",
        base_manifest_sha256="fixture",
        base_history_sha256="fixture",
    )
    (logs / "manifest.json").write_text(json.dumps(manifest))
    history = logs / "history.jsonl"
    history.write_text("".join(json.dumps(r) + "\n" for r in extra))
    monkeypatch.setattr(module, "validate_frozen", lambda _: ({}, base))
    module.render(tmp_path)
    table = (tmp_path / "tables/bfgs_reference.tex").read_text()
    assert "Quadratics = 1/1" in table
    assert "Method & CUTEst & Quadratics" not in table
    for result in extra:
        if result["method"] == module.BFGS:
            result.update(success=False, status="budget")
    history.write_text("".join(json.dumps(r) + "\n" for r in extra))
    module.render(tmp_path)
    report = (tmp_path / "REPORT.md").read_text()
    assert "| BFGS-SP | 0/1 | 0/1 | -- | 0 | 2 |" in report
    assert "Method only = 0" in report


def test_missing_entire_problem_stays_in_denominator():
    result = performance_profiles([row("present", "XR", 1)], ["XR", "XR-F"], ["present", "missing"])
    assert result["curves"]["XR"] == [0.5]
    assert result["curves"]["XR-F"] == [0]
    assert len(result["missing"]) == 3
    assert result["all_failed"] == ["missing"]


def test_empty_profile_and_duplicate_or_invalid_measurements():
    result = performance_profiles([], ["XR"], [])
    assert result["curves"]["XR"] == [0]
    with pytest.raises(ValueError, match="Duplicate result"):
        performance_profiles([row("p", "XR", 1)] * 2, ["XR"], ["p"])
    with pytest.raises(ValueError, match="positive and finite"):
        performance_profiles([row("p", "XR", 0)], ["XR"], ["p"])
    with pytest.raises(ValueError, match="unique"):
        performance_profiles([], ["XR", "XR"], [])


def test_render_exposes_partial_campaign_and_writes_only_small_final_artifacts(tmp_path):
    records = [row("p", "XR", 1), row("p", "XR-F", 2, success=False)]
    expected = [
        dict(problem="p", suite="cutest", group="sos-small", n=100),
        dict(problem="q", suite="cutest", group="sos-small", n=100),
    ]
    result = render(records, tmp_path, expected_methods=["XR", "XR-F"], expected_problems=expected)
    assert not result["complete"]
    assert result["missing"] == 2
    report = (tmp_path / "REPORT.md").read_text()
    assert "PARTIAL" in report
    assert "**1/2**" in report
    assert result["bytes"] < 500_000
    assert {p.suffix for p in tmp_path.rglob("*") if p.is_file()} <= {".pdf", ".tex", ".md"}
    assert (tmp_path / "figures/cutest_gradients.pdf").read_bytes().startswith(b"%PDF")
    table = (tmp_path / "tables/cutest_summary.tex").read_text()
    assert r"\begin{tabular}" in table and r"\caption{" in table


def test_render_rejects_outside_cohort_and_inconsistent_grouping(tmp_path):
    with pytest.raises(ValueError, match="outside the frozen"):
        render(
            [row("unexpected", "XR", 1)],
            tmp_path,
            expected_problems=[dict(problem="expected", suite="cutest")],
        )
    with pytest.raises(ValueError, match="Inconsistent problem metadata"):
        render([row("p", "XR", 1), row("p", "XR-F", 1, group="general-small")], tmp_path)
    with pytest.raises(ValueError, match="Unclassified"):
        render([row("p", "XR", 1, group="mystery")], tmp_path)


def test_ablations_pair_costs_and_expose_different_success_sets(tmp_path):
    records = [
        row("both", "XR-F", 2, suite="ablation"),
        row("both", "without_F", 8, suite="ablation"),
        row("base_only", "XR-F", 3, suite="ablation"),
        row("base_only", "without_F", 3, suite="ablation", success=False),
    ]
    result = render(records, tmp_path)
    assert result["complete"]
    table = (tmp_path / "tables/ablations.tex").read_text()
    assert r"without\_F & 1/2 & 4 & 1 & 1" in table
    assert "Variant only = 0" in table


def test_controlled_figure_uses_common_quantity_and_native_vector_output(tmp_path):
    records = [row("p", method, 3, suite="quadratic") for method in ("XR", "XR-F")]
    for record in records:
        record["trace"] = [
            dict(n_g=1, error=1.0, gnorm=2.0),
            dict(n_g=2, error=0.1, gnorm=0.2),
            dict(n_g=3, error=0.0, gnorm=0.0),
        ]
    result = render(records, tmp_path)
    assert result["complete"]
    assert (tmp_path / "figures/controlled.pdf").is_file()
    assert len(list((tmp_path / "figures").iterdir())) == 1


def test_full_perturbation_grid_does_not_impute_failure_costs(tmp_path):
    records = []
    cohort = []
    for seed in range(3):
        name = f"p{seed}"
        spec = {"kappa": 100, "epsilon": 0.1, "seed": seed, "n": 100}
        cohort.append(
            dict(problem=name, suite="perturbed", group="quadratic", n=100, problem_spec=spec)
        )
        if seed == 2:
            continue  # An entire missing scheduled seed still counts in the cell.
        for method, cost in (("XR-F", 2), ("L-BFGS", 8)):
            record = row(
                name,
                method,
                cost,
                suite="perturbed",
                group="quadratic",
                success=not (seed == 1 and method == "L-BFGS"),
            )
            record["problem_spec"] = spec
            records.append(record)
    grid = _perturbed_grid(records, cohort)
    assert grid["cells"][100, 0.1] == {
        "logratio": 2,
        "paired": 1,
        "n": 3,
        "ours_only": 1,
        "other_only": 0,
    }
    result = render(
        records, tmp_path, expected_methods=["XR-F", "L-BFGS"], expected_problems=cohort
    )
    assert result["missing"] == 2
    assert (tmp_path / "figures/controlled.pdf").exists()


def test_shared_heatmap_counts_require_identical_complete_pairs_and_no_exclusives():
    full = dict(n=3, paired=3, ours_only=0, other_only=0)
    assert _shared_full_pair_count({"a": full, "b": full}) == "3/3"
    assert _shared_full_pair_count({"a": full, "b": dict(full, paired=2)}) is None
    assert _shared_full_pair_count({"a": full, "b": dict(full, n=4, paired=4)}) is None
    assert _shared_full_pair_count({"a": dict(full, ours_only=1)}) is None
    assert _shared_full_pair_count({"a": dict(full, n=0, paired=0)}) is None
    assert _shared_full_pair_count({}) is None


def test_family_balancing_uses_explicit_sources_and_keeps_missing_weights():
    records = []
    cohort = []
    for problem, source, xr_cost, other_cost in (
        ("arbitrary-name-1", "FAMILY_A", 2, 4),
        ("different-prefix-2", "FAMILY_A", 2, 4),
        ("same-prefix-3", "FAMILY_B", 4, 2),
        ("same-prefix-4", "FAMILY_B", None, None),
    ):
        cohort.append(
            dict(
                problem=problem,
                suite="cutest",
                group="sos-small",
                n=100,
                problem_spec={"source": source},
            )
        )
        if xr_cost is not None:
            records.extend([row(problem, "XR", xr_cost), row(problem, "L-BFGS", other_cost)])
    result = _family_sensitivity(records, cohort, ["XR", "L-BFGS"])
    ours, other = result
    assert ours["n"] == 4 and ours["families"] == 2
    assert ours["raw_win"] == 0.5
    assert ours["family_win"] == 0.5
    assert other["family_win"] == 0.25
    assert ours["family_solved"] == other["family_solved"] == 0.75
    cohort[0]["problem_spec"] = {}
    assert _family_sensitivity(records, cohort, ["XR", "L-BFGS"]) == []


def test_all_failed_perturbation_cells_and_tex_escaping(tmp_path):
    records = []
    for method in ("XR-F", "L-BFGS"):
        record = row("p", method, 9, suite="perturbed", success=False)
        record["problem_spec"] = {"kappa": 100, "epsilon": 0.1, "seed": 0}
        record["label"] = method + "_custom & 20%"
        records.append(record)
    result = render(records, tmp_path)
    assert result["complete"]
    grid_table = (tmp_path / "tables/perturbations.tex").read_text()
    assert "0/1 & -- & 0 & 0" in grid_table
    summary = (tmp_path / "tables/perturbed_summary.tex").read_text()
    assert r"XR-F\_custom \& 20\%" in summary
    assert not list(tmp_path.rglob("*.png"))


def test_alias_observations_are_validated_not_counted_as_independent(tmp_path):
    original = row("P[N=100]", "XR-F", 4)
    original.update(
        job_id="original",
        problem_spec={"source": "P", "sif": {"N": 100}},
        info={
            "counters": {"nprobe": 2, "nrank_deleted": 3, "nF_applied": 4, "nF_fallback": 1},
            "mean_window": 2.5,
            "growing_memory": {"maximum": 10},
        },
    )
    alias = dict(
        original, problem="ablation:P[N=100]", suite="ablation", job_id="alias", alias_of="original"
    )
    result = render([original, alias], tmp_path)
    assert result["complete"]
    report = (tmp_path / "REPORT.md").read_text()
    assert "**1 distinct objective/start pairs**" in report
    assert "1 computed observations and 1 exact alias rows" in report
    assert "nF_applied=4" in report
    assert "accepted-iterate trajectories" in report
    assert (tmp_path / "tables/diagnostics.tex").is_file()
    assert "$N_f$" in (tmp_path / "tables/cutest_summary.tex").read_text()
    altered = dict(alias, n_g=5)
    with pytest.raises(ValueError, match="changed observed field n_g"):
        render([original, altered], tmp_path)
    with pytest.raises(ValueError, match="originally computed"):
        render([alias], tmp_path)


def test_manifest_revisions_and_concurrent_timing_are_disclosed(tmp_path):
    manifest = {
        "workers": 8,
        "source_hash": "current",
        "environment": {"blas_threads": 1},
        "revisions": [
            {
                "prior_source_hash": "prior",
                "reused_baseline_records": 394,
                "discarded_our_records": 267,
                "reason": "Direct Armijo and realized displacement.",
            }
        ],
    }
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    render([row("P", "XR", 4)], tmp_path)
    report = (tmp_path / "REPORT.md").read_text()
    assert "8 concurrent" in report
    assert "394 baseline records were reused" in report
    assert "267 earlier own-method observations" in report
    assert "not asserted to be the raw source fingerprint" in report


def test_development_strata_keep_failed_remaining_cases_and_disclose_baseline_reuse(tmp_path):
    records = []
    cohort = []
    for role in ("development", "pilot-diagnostic", "remaining-benchmark"):
        for method in ("XR", "L-BFGS"):
            record = row(role, method, 2, success=role != "remaining-benchmark")
            record["problem_spec"] = {"source": role, "development_role": role}
            records.append(record)
        cohort.append(
            dict(
                problem=role,
                suite="cutest",
                group="sos-small",
                n=100,
                problem_spec={"source": role, "development_role": role},
            )
        )
    strata = _development_sensitivity(records, cohort, ["XR", "L-BFGS"])
    assert len(strata) == 6
    assert strata[-1]["family_solved"] == 0
    manifest = {
        "baseline_reuse": {
            "policy": "Unchanged baselines only.",
            "records": [
                {"producer_source_hash": "producer-A"},
                {"producer_source_hash": "producer-B"},
            ],
        }
    }
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    render(records, tmp_path)
    report = (tmp_path / "REPORT.md").read_text()
    assert "**2 reused CUTEst baseline observations**" in report
    assert "Producer `producer-A`: 1 observations." in report
    assert "not an independent held-out validation claim" in report
    assert (tmp_path / "tables/cutest_development_sensitivity.tex").is_file()


def libsvm_cohort():
    return [
        dict(
            suite="libsvm",
            problem=f"libsvm:{dataset}:lambda={reg:g}",
            dataset=dataset,
            regularization=reg,
            n=n + 1,
            samples=samples,
            storage=storage,
            group=group,
        )
        for dataset, n, samples, storage, group in (
            ("a9a", 123, 32561, "csr", "moderate"),
            ("gisette", 5000, 6000, "dense", "dense-highdim"),
        )
        for reg in (0.01, 0.0001, 0.000001)
    ]


def test_libsvm_profiles_keep_missing_failures_and_generate_tables(tmp_path):
    cohort = libsvm_cohort()
    methods = ["XR", "XR-F", "L-CG_DESCENT"]
    records = []
    for i, problem in enumerate(cohort):
        for j, method in enumerate(methods):
            if i == 5:  # Entire scheduled problem absent.
                continue
            value = row(
                problem["problem"],
                method,
                10 + j,
                success=i != 4 and (i + j) % 4 != 1,
                suite="libsvm",
                group=problem["group"],
            )
            value.update(n=problem["n"], problem_spec=problem)
            records.append(value)
    result = render(
        records, tmp_path, expected_methods={"libsvm": methods}, expected_problems=cohort
    )
    assert result["missing"] == 3
    assert result["complete"] is False
    assert (tmp_path / "figures/libsvm.pdf").read_bytes().startswith(b"%PDF")
    datasets = (tmp_path / "tables/libsvm_datasets.tex").read_text()
    assert "32,561" in datasets and "5,000" in datasets and "gisette" in datasets
    assert "appended intercept" in datasets
    comparisons = (tmp_path / "tables/libsvm_comparisons.tex").read_text()
    assert "method/XR" in comparisons and "XR only" in comparisons
    assert "Each regularization level contains 2 scheduled datasets" in comparisons
    assert "All methods reach the target" not in comparisons
    assert "$10^{-6}$" in comparisons and "$1e-06$" not in comparisons
    assert len(result["libsvm_comparisons"]) == 6
    profile = performance_profiles(records, methods, [p["problem"] for p in cohort], suite="libsvm")
    assert len(profile["all_failed"]) == 2
    assert conditional_logit_profile(profile)["n"] == 4


def test_libsvm_render_empty_scheduled_campaign_is_explicit(tmp_path):
    cohort = libsvm_cohort()
    result = render(
        [], tmp_path, expected_methods={"libsvm": ["XR", "XR-F"]}, expected_problems=cohort
    )
    assert result["missing"] == 12
    assert result["complete"] is False
    assert (tmp_path / "figures/libsvm.pdf").exists()
    report = (tmp_path / "REPORT.md").read_text()
    assert "PARTIAL" in report
    assert "0/4 scheduled runs converged" in report
    assert "recorded-minimum counts are provisional" in report
    assert "minimum observed gradient count on 0/2 datasets" in report


def test_new_native_provenance_and_sequential_timing_are_manifest_driven(tmp_path):
    from xrbench.study import _implementation_description, _timing_description

    manifest = dict(
        workers=1,
        environment={"blas_threads": 1},
        native_backend={"build_key": "xr"},
        competitor_native_backend={"build_key": "all-c"},
    )
    assert "sequentially" in " ".join(_timing_description(manifest))
    assert "one timed run" in " ".join(_timing_description(manifest))
    assert "concurrent" not in " ".join(_timing_description(manifest))
    text = " ".join(_implementation_description(manifest))
    assert "our C implementations" in text
    assert "Python control with NumPy" not in text
    assert "all-c" in " ".join(_native_provenance(manifest, tmp_path))
    manifest["implementations"] = {"MS-L-BFGS": "C from published polar algorithm"}
    assert "C from published polar algorithm" in " ".join(_implementation_description(manifest))
    assert "Python control" in " ".join(_implementation_description({}))


def test_libsvm_regime_minima_count_ties_and_baseline_winners():
    from xrbench.study import _libsvm_outcomes

    problems = [p for p in libsvm_cohort() if p["regularization"] == 0.01]
    names = ["XR", "XR-F", "L-BFGS"]
    records = []
    for problem, counts, times in zip(
        problems, ((10, 12, 10), (11, 12, 8)), ((0.8, 0.5, 0.5), (0.8, 0.7, 0.4))
    ):
        for name, count, seconds in zip(names, counts, times):
            observation = row(problem["problem"], name, count, suite="libsvm")
            observation["seconds"] = seconds
            records.append(observation)
    (summary,) = _libsvm_outcomes(records, problems, names)
    assert summary["scheduled_runs"] == summary["converged_runs"] == 6
    assert summary["all_methods_solved"] == 2
    assert summary["xr_gradient_minima"] == summary["xr_time_minima"] == 1
    assert summary["datasets"] == 2 and summary["missing_runs"] == 0


def test_libsvm_regime_minima_preserve_failed_and_missing_denominators():
    from xrbench.study import _libsvm_outcomes

    names = ["XR", "XR-F", "L-BFGS"]
    problems = [
        dict(problem=name, regularization=0.0001)
        for name in ("all-failed", "baseline-only", "partial")
    ]
    records = [row("all-failed", name, 1, success=False, suite="libsvm") for name in names]
    records += [
        row("baseline-only", "XR-F", 1, success=False, suite="libsvm"),
        row("baseline-only", "L-BFGS", 1, suite="libsvm"),
        row("partial", "XR", 3, suite="libsvm"),
    ]
    (summary,) = _libsvm_outcomes(records, problems, names)
    assert summary["datasets"] == 3 and summary["scheduled_runs"] == 9
    assert summary["converged_runs"] == 2 and summary["missing_runs"] == 3
    assert summary["all_methods_solved"] == 0
    assert summary["xr_gradient_minima"] == summary["xr_time_minima"] == 1


def test_libsvm_success_caption_uses_completed_scheduled_counts(tmp_path):
    cohort = libsvm_cohort()
    methods = ["XR", "XR-F", "L-CG_DESCENT"]
    records = [
        dict(
            row(problem["problem"], method, 10 + j, suite="libsvm", group=problem["group"]),
            n=problem["n"], problem_spec=problem,
        )
        for problem in cohort
        for j, method in enumerate(methods)
    ]
    render(records, tmp_path, expected_methods={"libsvm": methods}, expected_problems=cohort)
    table = (tmp_path / "tables/libsvm_comparisons.tex").read_text()
    assert "All methods reach the target on all 2 datasets at each regularization level" in table
    assert "Both solved" not in table and "XR only" not in table
    assert "Common to all rows" not in table


def test_local_caption_retains_unsuccessful_or_missing_full_windows(tmp_path):
    config = local_config(seeds=(0, 1), methods=("XR",))
    records = [local_row(0), local_row(1, errors=(1, 1e-3), success=False)]
    records[1]["first_full_n_g"] = None
    render_local_study(records, tmp_path, config)
    table = (tmp_path / "tables/local_summary.tex").read_text()
    assert "All 2 runs reach the target" not in table
    assert "1/2" in table and "Full window" in table
