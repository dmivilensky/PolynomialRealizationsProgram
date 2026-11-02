"""Tests for methods/lbfgs_scipy.py (scipy L-BFGS-B, no bounds)."""

import numpy as np
import pytest
from _infra import Quad, run_gtol, run_method

from xrbench.methods import lbfgs_scipy


@pytest.mark.parametrize("m", [5, 10, 20])
def test_quadratic_n20_kappa1e3(m):
    r = run_gtol(lbfgs_scipy.solve, Quad(), dict(m=m))
    assert r["status"] == "converged", r["status"]
    assert r["n_it"] > 0


def test_internal_tests_off():
    """ftol = gtol = 0: L-BFGS-B does not stop by itself before a strict but attainable target (1e-9 relative);
    its only remaining internal stop is "no decrease of f at all" (factr * epsmch = 0), here at about 6e-10."""
    P = Quad()
    g0 = np.linalg.norm(P.grad(P.x0))
    r = run_method(lbfgs_scipy.solve, P, P.x0, {}, gtol=1e-9 * g0, budget=3000)
    assert r["status"] == "converged", (r["status"], r["info"])
