"""Native execution, accounting and cleanup beyond cold ModelStep algebra.

The physical-coordinate model reconstructions live in test_xr_native_model.
Here the independent Python executor and the common oracle check the actual
queries, rejection/probe control flow, accepted advances and exception identity.
"""

from dataclasses import asdict
from pathlib import Path

import numpy as np
import pytest

from xrbench.methods import xr, xr_native
from xrbench.native.build import backend_metadata
from xrbench.oracle import Budget, Converged, run_method
from xrbench.problems.synthetic import SmoothQuadratic


class StopTest(Exception):
    pass


class RecordingOracle:
    """A small actual oracle, also able to stop at a chosen callback boundary."""

    def __init__(self, *, flat=False, fail=None, failure=None, max_marks=3):
        self.flat = flat
        self.fail = fail
        self.failure = failure if failure is not None else StopTest("callback sentinel")
        self.max_marks = max_marks
        self.calls = []
        self.info = {}
        self.n_it = 0
        self.points = []

    def _visit(self, kind, x=None):
        self.calls.append(kind)
        if x is not None:
            # Retain the exact object: the native bridge must not expose freed
            # solver buffers, even if an oracle keeps its point arguments.
            self.points.append((x, np.asarray(x).copy()))
        if self.fail == (kind, self.calls.count(kind)):
            raise self.failure

    def fg(self, x):
        self._visit("fg", x)
        if self.flat:
            return 0.0, np.ones_like(x)
        return float(0.5 * x @ (np.array([1.0, 7.0]) * x)), np.array([1.0, 7.0]) * x

    def f(self, x):
        self._visit("f", x)
        return 0.0 if self.flat else float(0.5 * x @ (np.array([1.0, 7.0]) * x))

    def g(self, x):
        self._visit("g", x)
        return np.ones_like(x) if self.flat else np.array([1.0, 7.0]) * x

    def mark_iter(self):
        self.n_it += 1
        self._visit("mark")
        if self.n_it >= self.max_marks:
            raise self.failure

    def note(self, key, value):
        self.info[key] = value


@pytest.mark.parametrize(
    "policy",
    [
        {},
        {"values": True},
        {"values": True, "trial": "lagged"},
        {"values": True, "trial": "midpoint", "floor": True},
        {"values": True, "window": "positive"},
        {"values": True, "probe": False},
        {"values": True, "m_max": 3},
        {"values": True, "split": "euclidean"},
    ],
)
@pytest.mark.parametrize("perturbation", [0.0, 0.1])
def test_native_complete_solve_matches_reference_queries_and_targets(policy, perturbation):
    traces, results = [], []
    for solver in (xr.solve, xr_native.solve):
        problem = SmoothQuadratic(10, 30.0, perturbation, 1)
        trace = []
        results.append(
            run_method(
                solver,
                problem,
                problem.x0,
                dict(m0=3, m_max=10, trace=trace) | policy,
                budget=2000,
                max_time=20,
                relative_gtol=1e-8,
            )
        )
        traces.append(trace)
    assert all(row["status"] == "converged" for row in results)
    # Core kernels may differ by rounding, but these resolved cases should
    # use the same actual evaluations and acceptance/probe decisions.
    for key in ("n_pts", "n_f_evals", "n_g_evals", "n_it"):
        assert results[0][key] == results[1][key]
    assert results[0]["info"]["growing_memory"] == results[1]["info"]["growing_memory"]
    assert results[0]["info"]["counters"] == results[1]["info"]["counters"]
    assert len(traces[0]) == len(traces[1])
    for expected, actual in zip(*traces, strict=True):
        for key in (
            "iteration",
            "evaluation",
            "accepted",
            "window",
            "capacity",
            "gradient_evaluated",
        ):
            assert expected[key] == actual[key]
        np.testing.assert_allclose(actual["value"], expected["value"], atol=2e-14, rtol=1e-8)


@pytest.mark.parametrize("probe", [False, True])
def test_rejected_scalar_trials_do_not_request_hidden_gradients(probe):
    oracle = RecordingOracle(flat=True)
    xr_native.solve(oracle, np.ones(2), m0=1, m_max=2, probe=probe, maxbt=3)
    assert oracle.info["stop"] == "backtracking_limit"
    assert oracle.calls.count("fg") == (2 if probe else 1)
    assert oracle.calls.count("f") == (2 if probe else 3)
    assert oracle.calls.count("g") == 0
    assert oracle.info["counters"]["nprobe"] == int(probe)
    assert oracle.info["counters"]["nrej"] == 3
    assert oracle.info["counters"]["nbt"] == (2 if probe else 3)


@pytest.mark.parametrize(
    "boundary,probe",
    [
        (("fg", 1), True),
        (("fg", 2), True),
        (("f", 1), False),
        (("g", 1), False),
        (("mark", 1), True),
    ],
)
@pytest.mark.parametrize("exception_type", [StopTest, Budget, Converged])
def test_callback_exceptions_preserve_identity_after_cleanup(boundary, probe, exception_type):
    failure = exception_type("original callback exception")
    oracle = RecordingOracle(fail=boundary, failure=failure)
    with pytest.raises(exception_type) as error:
        xr_native.solve(oracle, np.ones(2), m0=1, m_max=2, probe=probe)
    assert error.value is failure
    if boundary != ("fg", 1):
        assert "counters" in oracle.info and "growing_memory" in oracle.info
    for point, saved in oracle.points:
        np.testing.assert_array_equal(point, saved)
    # Exercise repeated free paths, then a normal solve in the same process.
    problem = SmoothQuadratic(4, 5.0, 0.0, 2)
    row = run_method(xr_native.solve, problem, problem.x0, {}, budget=100, relative_gtol=1e-8)
    assert row["status"] == "converged"


def test_accepted_hook_sees_used_model_window_and_owns_arrays():
    oracle = RecordingOracle(max_marks=100)
    trace, seen = [], []
    failure = StopTest("accepted observer target")

    def accepted(x, f, g, info):
        accepted_trace = [record for record in trace if record["accepted"]]
        assert info["window"] == accepted_trace[-1]["window"]
        assert info["iteration"] == len(accepted_trace) == oracle.n_it
        assert f == pytest.approx(0.5 * x @ (np.array([1.0, 7.0]) * x))
        np.testing.assert_allclose(g, np.array([1.0, 7.0]) * x)
        seen.append((x.copy(), g.copy()))
        x[:] = 1e100
        g[:] = np.nan
        if len(seen) == 2:
            raise failure

    with pytest.raises(StopTest) as error:
        xr_native.solve(oracle, np.ones(2), m0=1, m_max=2, trace=trace, accepted_hook=accepted)
    assert error.value is failure and len(seen) == 2
    assert all(np.all(np.isfinite(x)) for x, _ in seen)
    assert oracle.info["counters"]["nnumerical"] == 0


def test_common_point_budget_is_unchanged_by_native_initialization():
    problem = SmoothQuadratic(5, 10.0, 0.0, 1)
    row = run_method(xr_native.solve, problem, problem.x0, {}, budget=1, relative_gtol=1e-14)
    assert row["status"] == "budget"
    assert row["n_pts"] == row["n_fg_evals"] == row["n_g_evals"] == row["n_f_evals"] == 1
    assert "counters" in row["info"]


@pytest.mark.parametrize(
    "key,value",
    [
        ("m0", -1),
        ("m_max", 0),
        ("q", 0),
        ("theta", np.inf),
        ("noise_multiplier", np.nan),
        ("window", "typo"),
        ("split", "typo"),
        ("trial", "typo"),
    ],
)
def test_private_native_boundary_rejects_invalid_parameters_before_allocation(key, value):
    params = asdict(xr.Parameters()) | {key: value}
    data = dict(x=np.zeros(2), g=np.ones(2), f=0.0)
    with pytest.raises(ValueError):
        xr_native._native.debug_model(data, params)
    with pytest.raises(ValueError):
        xr_native._native.solve(RecordingOracle(), np.ones(2), params)


def test_missing_native_policy_is_a_python_exception():
    params = asdict(xr.Parameters())
    del params["trial"]
    with pytest.raises(ValueError, match="Missing"):
        xr_native._native.debug_model(dict(x=np.zeros(2), g=np.ones(2), f=0.0), params)


@pytest.mark.parametrize("maxbt", [0, -1, 1.5])
def test_invalid_execution_limit_is_rejected(maxbt):
    with pytest.raises(ValueError, match="maxbt"):
        xr_native.solve(RecordingOracle(), np.ones(2), maxbt=maxbt)


def test_build_provenance_and_compilation_are_outside_solve(monkeypatch):
    metadata = backend_metadata()
    assert {
        "xr_model.c",
        "xr_bridge.c",
        "xr_executor.c",
        "xr_native.h",
        "xr_executor.h",
    } <= metadata["source_files"].keys()
    assert "-fno-fast-math" in metadata["flags"] and "-ffp-contract=off" in metadata["flags"]
    assert len(metadata["extension_sha256"]) == len(metadata["build_key"]) == 64
    assert not Path(xr_native._native.__file__).is_relative_to(Path(__file__).parents[1])

    def compiler_must_not_run(*args, **kwargs):
        raise AssertionError("Compilation inside native solve")

    monkeypatch.setattr("xrbench.native.build.subprocess.run", compiler_must_not_run)
    problem = SmoothQuadratic(4, 5.0, 0.0, 2)
    row = run_method(xr_native.solve, problem, problem.x0, {}, budget=100, relative_gtol=1e-8)
    assert row["status"] == "converged"
