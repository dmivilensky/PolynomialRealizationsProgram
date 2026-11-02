"""Tests for methods/oaccel.py (O-ACCEL, Riseth 2019; N-GMRES, De Sterck 2012/2013).

Identities tested (on f = x^T A x / 2 - b^T x, A SPD, n = 20, kappa = 1e3):
  * Riseth 2019, Sec. 2.2, Theorem 1 / Lemma 1 (eq. (16)): with a steepest-descent preconditioner and
    no reset, the O-ACCEL iterates are the FOM iterates of A x = b started at x^(1), and FOM = CG for SPD A:
    x^(k+1) = argmin { f(x) : x in x^(1) + K_k(A, r^(1)) }.  The theorem concerns the unregularized
    system (8)/(10), so it is tested with eps0 = 0; the published eps0 = 1e-12 is tested with a looser bound.
    With Option A (exact line search along -g on a quadratic) a window of one point gives x^A = x^P and the
    descent test of Alg. 1 resets; the theorem then applies from the last reset point.
"""

import numpy as np
import pytest

from xrbench.methods.oaccel import _more_thuente, solve  # noqa: E402
from xrbench.oracle import Budget, Oracle, run_method  # noqa: E402


class Quad:
    """Strictly convex quadratic f = x^T A x / 2 - b^T x, eigenvalues log-spaced in [1, kappa]."""

    def __init__(self, n=20, kappa=1e3, seed=0):
        rng = np.random.default_rng(seed)
        Qm, _ = np.linalg.qr(rng.standard_normal((n, n)))
        lam = np.logspace(0.0, np.log10(kappa), n)
        A = (Qm * lam) @ Qm.T
        self.A = 0.5 * (A + A.T)
        self.b = rng.standard_normal(n)
        self.n = n
        self.xs = np.linalg.solve(self.A, self.b)
        self.fstar = float(self.f(self.xs))
        self.x0 = rng.standard_normal(n)
        self.name = "QUAD_%d_%g" % (n, kappa)
        self.err_from_f = True
        self.convex = True
        self.meta = dict(kappa=kappa, seed=seed)

    def f(self, x):
        return 0.5 * x @ self.A @ x - self.b @ x

    def grad(self, x):
        return self.A @ x - self.b

    def fg(self, x):
        Ax = self.A @ x
        return 0.5 * x @ Ax - self.b @ x, Ax - self.b

    def err_f(self, fx):
        return fx - self.fstar

    def err(self, x):
        return self.f(x) - self.fstar


class Rosenbrock:
    """Chained Rosenbrock (scipy.optimize.rosen), n = 10, x0 = (-1.2, 1, -1.2, 1, ...)."""

    def __init__(self, n=10):
        from scipy.optimize import rosen, rosen_der

        self._f, self._g = rosen, rosen_der
        self.n = n
        self.x0 = np.tile([-1.2, 1.0], n // 2)
        self.fstar = 0.0
        self.name = "ROS%d" % n
        self.err_from_f = True
        self.convex = False
        self.meta = {}

    def f(self, x):
        return self._f(x)

    def grad(self, x):
        return self._g(x)

    def err_f(self, fx):
        return fx


def _krylov_basis(A, r0, k):
    """Orthonormal basis of K_k(A, r0) (Arnoldi with two passes of Gram-Schmidt)."""
    V = np.zeros((r0.size, k))
    V[:, 0] = r0 / np.linalg.norm(r0)
    for j in range(1, k):
        w = A @ V[:, j - 1]
        for _ in range(2):
            w -= V[:, :j] @ (V[:, :j].T @ w)
        V[:, j] = w / np.linalg.norm(w)
    return V


def cg_iterate(p, x1, k):
    """k-th CG (= FOM for SPD A) iterate from x1: Galerkin point on x1 + K_k(A, r1)."""
    r1 = p.b - p.A @ x1
    V = _krylov_basis(p.A, r1, k)
    return x1 + V @ np.linalg.solve(V.T @ p.A @ V, V.T @ r1)


def _run(p, gtol_rel=1e-8, budget=5000, **params):
    tr = []
    g0 = np.linalg.norm(p.grad(p.x0))
    res = run_method(solve, p, p.x0, dict(params, trace=tr), budget=budget, gtol=gtol_rel * g0)
    return res, tr


# ----------------------------------------------------------------------------------- convergence
@pytest.mark.parametrize("nonlinear", ["oaccel"])
@pytest.mark.parametrize("precond", ["A", "B"])
def test_quadratic_reaches_gtol(nonlinear, precond):
    p = Quad()
    res, _ = _run(p, nonlinear=nonlinear, precond=precond)
    assert res["status"] == "converged", res["status"]
    assert res["best_gn"] <= 1e-8 * np.linalg.norm(p.grad(p.x0))


@pytest.mark.parametrize("nonlinear", ["oaccel"])
@pytest.mark.parametrize("precond", ["A", "B"])
def test_rosenbrock_n10_converges(nonlinear, precond):
    p = Rosenbrock(10)
    res, _ = _run(p, budget=20000, nonlinear=nonlinear, precond=precond)
    assert res["status"] == "converged", res["status"]
    assert res["best_f"] < 1e-8  # the global minimizer (1, ..., 1), not the second stationary point


# ----------------------------------------------------------------------- Riseth Thm 1 (FOM = CG)
def test_oaccel_optionB_is_cg_riseth_thm1():
    """Option B (x^P = x - delta g/||g||, eq. (30)), eps0 = 0: x^(k+1) = CG_k from x^(1) = x0 for k <= 16,
    with no reset and the unit step along x^A - x^P accepted (x^(k+1) = x^A)."""
    p = Quad()
    E0 = np.linalg.norm(p.x0 - p.xs)
    _, tr = _run(p, nonlinear="oaccel", precond="B", eps0=0.0)
    for k in range(1, 17):
        t = tr[k - 1]
        assert not t["restart"] and t["curw"] == min(k, 20)
        assert np.linalg.norm(t["x"] - t["x_A"]) <= 1e-12 * E0  # line search took lambda = 1
        assert np.linalg.norm(t["x"] - cg_iterate(p, p.x0, k)) <= 1e-6 * E0, k


def test_oaccel_optionB_published_eps0_close_to_cg():
    """With the published eps0 = 1e-12 the Tikhonov shift eps0*max_i A_ii (eq. (21)) acts on the newest
    column, whose diagonal entry is O(delta^2) = 1e-8 times smaller; the iterates stay within 1e-2
    of CG."""
    p = Quad()
    E0 = np.linalg.norm(p.x0 - p.xs)
    _, tr = _run(p, nonlinear="oaccel", precond="B")
    for k in range(1, 17):
        assert np.linalg.norm(tr[k - 1]["x"] - cg_iterate(p, p.x0, k)) <= 1e-2 * E0, k


@pytest.mark.parametrize("eps0", [0.0, 1e-12])
def test_oaccel_optionA_is_cg_after_last_reset(eps0):
    """Option A (eq. (29), More-Thuente along -g/||g||).  On a quadratic the line search lands on the
    exact line minimizer, so with a one-point window b = -(x_1 - x^P)^T g^P = 0 up to rounding and
    x^A = x^P: Alg. 1 may reset.  After the last early reset at iteration k_r, Theorem 1 applies with
    x^(1) := x^(k_r+1): x^(k_r+m+1) = CG_m from that point."""
    p = Quad()
    E0 = np.linalg.norm(p.x0 - p.xs)
    _, tr = _run(p, nonlinear="oaccel", precond="A", eps0=eps0)
    resets = [k for k, t in enumerate(tr, start=1) if t["restart"]]
    early = [k for k in resets if k <= 6]
    assert resets == early  # no reset once the window has >= 2 points
    kr = max(early, default=0)
    base = p.x0 if kr == 0 else tr[kr - 1]["x"]
    for m in range(1, 17):
        t = tr[kr + m - 1]
        assert np.linalg.norm(t["x"] - cg_iterate(p, base, m)) <= 1e-8 * E0, m


# --------------------------------------------------------------------------------- harness rules
def test_more_thuente_strong_wolfe_and_counting():
    p = Quad()
    O = Oracle(p, budget=100)
    x = p.x0
    f0, g0 = p.fg(x)
    d = -g0 / np.linalg.norm(g0)
    t, xt, ft, gt = _more_thuente(
        O, x, f0, g0, d, 1.0, c1=1e-4, c2=0.1, xtol=1e-8, stpmin=1e-16, stpmax=65536.0, maxfev=20
    )
    assert ft <= f0 + 1e-4 * t * (g0 @ d)  # sufficient decrease
    assert abs(gt @ d) <= 0.1 * abs(g0 @ d)  # strong curvature condition
    assert np.allclose(xt, x + t * d)
    assert O.n_f == O.n_g == O.n_pts <= 20  # every trial is one O.fg call at a new point
    assert (
        _more_thuente(
            O,
            x,
            f0,
            g0,
            -d,
            1.0,
            c1=1e-4,
            c2=0.1,
            xtol=1e-8,
            stpmin=1e-16,
            stpmax=65536.0,
            maxfev=20,
        )
        is None
    )  # ascent direction


class _StrictOracle:
    """Exposes only the oracle API a method may use (f, g, fg, mark_iter; no optional note)."""

    def __init__(self, O):
        self.f, self.g, self.fg, self.mark_iter = O.f, O.g, O.fg, O.mark_iter


@pytest.mark.parametrize("nonlinear", ["oaccel"])
@pytest.mark.parametrize("precond", ["A", "B"])
def test_budget_exception_propagates_and_only_oracle_api(nonlinear, precond):
    p = Rosenbrock(10)
    O = Oracle(p, budget=37)
    with pytest.raises(Budget):
        solve(_StrictOracle(O), p.x0.copy(), nonlinear=nonlinear, precond=precond)
    assert O.status == "budget" and O.n_pts <= 38 and O.n_it > 0
    res = run_method(solve, p, p.x0, dict(nonlinear=nonlinear, precond=precond), budget=37)
    assert res["status"] == "budget"
