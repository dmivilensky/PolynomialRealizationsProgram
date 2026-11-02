"""Tests for methods/cgdescent.py (CG_DESCENT 6.8 / L-CG_DESCENT via pycgdescent)."""

import pytest
from _infra import Quad, run_gtol, run_method

from xrbench.methods import cgdescent


@pytest.mark.parametrize("memory", [0, 11])
def test_quadratic_n20_kappa1e3(memory):
    r = run_gtol(cgdescent.solve, Quad(), dict(memory=memory))
    assert r["status"] == "converged", r["status"]


@pytest.mark.parametrize("budget", [1, 5, 13])
def test_budget_stop_propagates_through_c(budget):
    """The oracle's Budget exception propagates out of the C code and the count is exact."""
    P = Quad()
    r = run_method(cgdescent.solve, P, P.x0, {}, gtol=0.0, budget=budget)
    assert r["status"] == "budget" and r["n_pts"] == budget


def test_domain_problem_starts():
    """Regression: a non-zeroed work array made CG_DESCENT stop at x0 (status 11) on the log-barrier problem."""
    from xrbench.problems.synthetic import LogBarrier

    P = LogBarrier()
    r = run_method(cgdescent.solve, P, P.x0, {}, relative_gtol=1e-8, budget=20000)
    assert r["status"] == "converged", (r["status"], r["info"])
