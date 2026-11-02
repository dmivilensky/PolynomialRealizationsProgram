"""Tests for methods/bfgs_sp.py (BFGS with Shanno-Phua scaling and More-Thuente line search)."""

import numpy as np
from _infra import Quad, run_gtol

from xrbench.methods import bfgs_sp
from xrbench.oracle import Oracle


def test_quadratic_n20_kappa1e3():
    r = run_gtol(bfgs_sp.solve, Quad())
    assert r["status"] == "converged", r["status"]


def test_line_search_strong_wolfe():
    """The returned step satisfies the strong Wolfe conditions (c1 = 1e-4, c2 = 0.9)."""
    P = Quad()
    O = Oracle(P, budget=10**6)
    rng = np.random.default_rng(2)
    for _ in range(10):
        x = rng.normal(size=P.n)
        f, g = O.fg(x)
        d = -g + 0.3 * rng.normal(size=P.n)
        if g @ d >= 0:
            d = -g
        for a0 in (1e-3, 1.0 / np.max(np.abs(g)), 10.0):
            a, xn, fn, gn = bfgs_sp.wolfe_ls(O, x, d, f, g, a0, c1=1e-4, c2=0.9)
            assert fn <= f + 1e-4 * a * (g @ d) + 1e-12 * abs(f)
            assert abs(gn @ d) <= 0.9 * abs(g @ d) * (1 + 1e-10)


def test_bfgs_update_secant():
    """The expanded O(n^2) update equals the product form and satisfies H+ y = s."""
    rng = np.random.default_rng(0)
    n = 7
    B = rng.normal(size=(n, n))
    H = B @ B.T + np.eye(n)
    s, y = rng.normal(size=n), rng.normal(size=n)
    if s @ y < 0:
        y = -y
    rho = 1 / (s @ y)
    V = np.eye(n) - rho * np.outer(s, y)
    H1 = V @ H @ V.T + rho * np.outer(s, s)
    Hy = H @ y
    H2 = (
        H
        - rho * (np.outer(s, Hy) + np.outer(Hy, s))
        + (rho * rho * (y @ Hy) + rho) * np.outer(s, s)
    )
    assert np.allclose(H1, H2) and np.allclose(H2 @ y, s)
