"""Tests for oracle.py (counting, stopping, the 2026-10-15 fixes and extensions)."""

import numpy as np
from _infra import Quad

from xrbench.oracle import Oracle, run_method


class ErrFOnly:
    """A problem with err_f but no err (regression: such problems never converged on err_tol)."""

    err_from_f = True

    def __init__(self):
        self.n = 3
        self.x0 = np.ones(3)
        self.fstar = 0.0

    def f(self, x):
        return float(x @ x)

    def grad(self, x):
        return 2 * x

    def err_f(self, fx):
        return fx - self.fstar


def _gd(O, x0, step=0.25):
    x = x0.copy()
    while True:
        f, g = O.fg(x)
        x = x - step * g


def test_err_f_only_problem_converges():
    r = run_method(_gd, ErrFOnly(), np.ones(3), err_tol=1e-10)
    assert r["status"] == "converged"


def test_point_merging_and_counts():
    P = Quad()
    O = Oracle(P)
    x = P.x0
    O.f(x)
    O.g(x)
    O.fg(x)
    assert (O.n_pts, O.n_f, O.n_g) == (1, 2, 2)
    O.f(x + 1)
    assert O.n_pts == 2


def test_hvp_counts_as_point():
    P = Quad()
    O = Oracle(P)
    O.fg(P.x0)
    O.hvp(P.x0, P.x0)
    O.hvp(P.x0, P.x0)
    assert (O.n_pts, O.n_g, O.n_hv) == (3, 3, 2)


def test_budget_exact():
    r = run_method(_gd, Quad(), Quad().x0, gtol=0.0, budget=11)
    assert r["status"] == "budget" and r["n_pts"] == 11


def test_milestones():
    P = Quad()
    g0 = np.linalg.norm(P.grad(P.x0))
    r = run_method(
        _gd, P, P.x0, dict(step=1e-3), gtol=1e-6 * g0, g_levels=[1e-2 * g0, 1e-4 * g0], budget=10**6
    )
    ms = r["milestones"]["g"]
    assert r["status"] == "converged" and len(ms) == 2
    a, b = sorted(v[0] for v in ms.values())
    assert 0 < a < b <= r["n_pts"]


def test_note_and_info():
    def m(O, x0):
        O.note("stop", "test")
        O.fg(x0)

    r = run_method(m, Quad(), Quad().x0)
    assert r["status"] == "method_stop" and r["info"]["stop"] == "test"
