"""Tests for methods/mslbfgs.py (Gubarev 2026, MS-L-BFGS).

Identities checked (equation numbers of F. V. Gubarev, "A Multi-Secant Limited-Memory BFGS Method",
Optimization Online, March 2026):
  * O = S^T Y symmetric positive definite  ->  update (9) (and (14)) is Schnabel's block BFGS, H Y = S;
  * general (non-symmetric) O: H Y = S Omega with Omega = K_R^{-1} O orthogonal (11); the direct update
    (10) is the inverse of (9); the exact variant (14)-(16) satisfies the newest secant exactly;
  * limited-memory compact form == dense recursion of the retained block updates; B H = I;
  * M = 1 with positive curvature and no damping == L-BFGS two-loop recursion with the same H0;
  * on a quadratic (exact pairs) the newest window's secant equations H Y_q = S_q hold at every iteration;
  * convergence: convex quadratic (n = 20, kappa = 1e3) to ||g|| <= 1e-8 ||g0||; Rosenbrock n = 10;
  * paper claim (Sec. 5.1, Fig. 2): on random diagonal quadratics (kappa = 1e6, eigenvalues uniform in
    [1, kappa], x0 = ones, stopping rule (47)) M <= L/2 behaves like L-BFGS-B and M = L = 8 needs
    clearly fewer gradient evaluations.
"""

import numpy as np
import pytest

from xrbench.methods import mslbfgs as ms  # noqa: E402
from xrbench.oracle import Converged, Oracle, run_method  # noqa: E402


# ----------------------------------------------------------------------------------------- problems
class Quad:
    """f = 1/2 (x - x*)^T A (x - x*), A = Q diag(logspace(0, log10 kappa)) Q^T  (f* = 0 exactly)."""

    def __init__(self, n=20, kappa=1e3, seed=0):
        rng = np.random.default_rng(seed)
        Q, _ = np.linalg.qr(rng.standard_normal((n, n)))
        lam = np.logspace(0.0, np.log10(kappa), n)
        self.A = (Q * lam) @ Q.T
        self.n = n
        self.xs = rng.standard_normal(n)
        self.x0 = np.zeros(n)
        self.fstar = 0.0

    def f(self, x):
        e = x - self.xs
        return 0.5 * e @ (self.A @ e)

    def grad(self, x):
        return self.A @ (x - self.xs)

    def err_f(self, v):
        return v


class Rosenbrock:
    def __init__(self, n=10):
        self.n = n
        self.x0 = np.tile([-1.2, 1.0], n // 2)
        self.fstar = 0.0

    def f(self, x):
        return float(np.sum(100 * (x[1:] - x[:-1] ** 2) ** 2 + (1 - x[:-1]) ** 2))

    def grad(self, x):
        g = np.zeros_like(x)
        t = x[1:] - x[:-1] ** 2
        g[:-1] = -400 * x[:-1] * t - 2 * (1 - x[:-1])
        g[1:] += 200 * t
        return g

    def err_f(self, v):
        return v


def _spd(n, rng, cond=10.0):
    Q, _ = np.linalg.qr(rng.standard_normal((n, n)))
    return (Q * np.logspace(0, np.log10(cond), n)) @ Q.T


# ---------------------------------------------------------------------------- algebraic identities
@pytest.mark.parametrize("exact", [False, True])
def test_symmetric_O_reduces_to_block_bfgs(exact):
    rng = np.random.default_rng(1)
    n, q = 12, 4
    A = _spd(n, rng, 100.0)
    S = rng.standard_normal((n, q))
    Y = A @ S  # O = S^T A S symmetric positive definite
    H0 = _spd(n, rng, 5.0)
    O = S.T @ Y
    Oi = np.linalg.inv(O)
    P = np.eye(n) - Y @ Oi @ S.T
    H_block = P.T @ H0 @ P + S @ Oi @ S.T  # Schnabel's block BFGS (inverse form)
    H = ms.ms_bfgs_update_H(H0, S, Y, exact_last=exact)
    assert np.allclose(H, H_block, atol=1e-10 * np.abs(H_block).max())
    assert np.allclose(H @ Y, S, atol=1e-10 * np.abs(S).max())  # secant equations H Y = S
    B = ms.ms_bfgs_update_B(np.linalg.inv(H0), S, Y, exact_last=exact)
    assert np.allclose(B @ H, np.eye(n), atol=1e-9)  # (10) is the inverse of (9)
    # the polar kernels coincide with O
    KR, KL = ms.polar_kernels(O)[:2]
    assert np.allclose(KR, O) and np.allclose(KL, O)


@pytest.mark.parametrize("exact", [False, True])
def test_nonsymmetric_O_polar_secants(exact):
    rng = np.random.default_rng(2)
    n, q = 15, 5
    S = rng.standard_normal((n, q))
    Y = _spd(n, rng, 10.0) @ S + 0.6 * rng.standard_normal((n, q))  # O non-symmetric
    O = S.T @ Y
    if O[-1, -1] <= 0:  # exact variant needs s^T y > 0
        Y[:, -1] *= -1
        O = S.T @ Y
    assert np.abs(O - O.T).max() > 0.1
    H0 = _spd(n, rng, 5.0)
    H = ms.ms_bfgs_update_H(H0, S, Y, exact_last=exact)
    assert np.all(np.linalg.eigvalsh(0.5 * (H + H.T)) > 0)  # positivity is automatic
    KR = ms.polar_kernels(O)[0]
    Om = np.linalg.solve(KR, O)  # Omega = K_R^{-1} O, eq. (11)
    assert np.allclose(Om @ Om.T, np.eye(q), atol=1e-10)
    if exact:
        assert np.allclose(H @ Y[:, -1], S[:, -1], atol=1e-10)  # newest secant exact, (12)-(14)
        assert not np.allclose(H @ Y, S, atol=1e-3)
    else:
        assert np.allclose(H @ Y, S @ Om, atol=1e-10)  # H Y = S Omega, eq. (11)
    B = ms.ms_bfgs_update_B(np.linalg.inv(H0), S, Y, exact_last=exact)
    assert np.allclose(B @ H, np.eye(n), atol=1e-8)  # (10)/(16) inverse of (9)/(14)
    # compact kernels (reversed Cholesky, eq. (42)) agree with the dense formulas (14)-(16)
    Ninv, C, rR = ms._kernels(O, exact)
    assert np.allclose(np.triu(rR), rR) and np.allclose(rR @ rR.T, KR)
    Hc = (np.eye(n) - S @ np.linalg.solve(O.T, Y.T)) @ H0 @ (
        np.eye(n) - Y @ np.linalg.solve(O, S.T)
    ) + S @ Ninv @ S.T
    assert np.allclose(Hc, H, atol=1e-10 * np.abs(H).max())
    assert np.allclose(np.linalg.inv(C), O.T @ Ninv @ O, atol=1e-8 * np.abs(C).max())


def _dense_from_approx(ap):
    """Dense recursion H_j = P_j^T H_{j-1} P_j + S_j K_j^{-1} S_j^T over the retained updates."""
    n = ap.n
    H = ap.gamma * np.eye(n)
    for lo, q, Ninv, C in ap.updates:
        w = np.arange(lo - ap.first_id, lo - ap.first_id + q)
        S, Y = ap.S[:, w], ap.Y[:, w]
        P = np.eye(n) - Y @ np.linalg.solve(S.T @ Y, S.T)
        H = P.T @ H @ P + S @ Ninv @ S.T
    return H


@pytest.mark.parametrize("M,exact", [(1, False), (3, False), (6, False), (3, True), (6, True)])
def test_compact_form_equals_dense_recursion(M, exact):
    rng = np.random.default_rng(3)
    n = 10
    ap = ms.MSLBFGSApprox(n, memory=6, M=M, exact_last=exact)
    A = _spd(n, rng, 50.0)
    for k in range(25):  # pairs from a non-quadratic-like perturbed model
        s = rng.standard_normal(n)
        y = A @ s + 0.3 * rng.standard_normal(n) * np.linalg.norm(A @ s) / np.sqrt(n)
        ap.update(s, y)
        Hd = _dense_from_approx(ap)
        Hc = ap.H(np.eye(n))
        assert np.allclose(Hc, Hd, atol=1e-9 * np.abs(Hd).max())
        Bc = ap.B(np.eye(n))
        assert np.allclose(Bc @ Hc, np.eye(n), atol=1e-7)
        assert np.all(np.linalg.eigvalsh(0.5 * (Hc + Hc.T)) > 0)
        assert ap.S.shape[1] <= 6
        # every retained window lies inside the stored pairs (truncation at block starts, Fig. 1)
        assert all(lo >= ap.first_id and lo + q <= ap.next_id for lo, q, _, _ in ap.updates)


def test_M1_equals_lbfgs_two_loop():
    rng = np.random.default_rng(4)
    n, mem = 15, 5
    A = _spd(n, rng, 30.0)
    ap = ms.MSLBFGSApprox(n, memory=mem, M=1)
    pairs = []
    for k in range(12):
        s = rng.standard_normal(n)
        y = A @ s
        ap.update(s, y)
        pairs.append((s, y))
    assert ap.n_damped == 0
    v = rng.standard_normal(n)
    # two-loop recursion with H0 = (s^T y / y^T y) I of the newest pair (= gamma*, Sec. 4.4)
    P = pairs[-mem:]
    q = v.copy()
    al = []
    for s, y in reversed(P):
        a = (s @ q) / (s @ y)
        al.append(a)
        q -= a * y
    s, y = P[-1]
    r = (s @ y) / (y @ y) * q
    for (s, y), a in zip(P, reversed(al)):
        b = (y @ r) / (s @ y)
        r += (a - b) * s
    assert np.allclose(ap.H(v), r, atol=1e-10 * np.abs(r).max())


def test_damping_restores_condition_20():
    rng = np.random.default_rng(5)
    for trial in range(30):
        p, q = np.exp(rng.uniform(-3, 3, 2))
        c = rng.uniform(-1, 1) * np.sqrt(p * q) * rng.choice([1e-3, 0.05, 0.5])
        for positive in (False, True):
            sign = 1.0 if (positive or c >= 0) else -1.0
            cc = sign * c
            th = ms.damping_thetas(p, q, cc)
            assert th is not None
            a, b = th
            assert 0 <= a <= 0.5 and 0 <= b <= 0.5
            c2 = cc * ((1 - a) * (1 - b) + a * b) + (1 - a) * b * p + a * (1 - b) * q
            p2 = (1 - a) ** 2 * p + 2 * a * (1 - a) * cc + a * a * q
            q2 = (1 - b) ** 2 * q + 2 * b * (1 - b) * cc + b * b * p
            tol = 1e-9 * (p + q)
            assert c2 >= ms.EPS_S * p2 - tol and c2 >= ms.EPS_Y * q2 - tol  # (20) after (21)
            # minimality: no feasible point of smaller norm on a coarse grid
            grid = np.linspace(0, 0.5, 101)
            Aa, Bb = np.meshgrid(grid, grid)
            C2 = cc * ((1 - Aa) * (1 - Bb) + Aa * Bb) + (1 - Aa) * Bb * p + Aa * (1 - Bb) * q
            P2 = (1 - Aa) ** 2 * p + 2 * Aa * (1 - Aa) * cc + Aa**2 * q
            Q2 = (1 - Bb) ** 2 * q + 2 * Bb * (1 - Bb) * cc + Bb**2 * p
            feas = (C2 >= ms.EPS_S * P2) & (C2 >= ms.EPS_Y * Q2)
            assert a * a + b * b <= np.min((Aa**2 + Bb**2)[feas]) + 1e-6


def test_gubarev_window():
    rng = np.random.default_rng(6)
    n = 30
    A = _spd(n, rng, 10.0)
    S = np.linalg.qr(rng.standard_normal((n, 6)))[0] * rng.uniform(0.5, 2.0, 6)
    Y = A @ S
    assert ms.gubarev_window(S, Y) == 0  # well-conditioned quadratic data: keep all
    Y2 = Y.copy()
    Y2[:, 0] = -Y[:, 1] * 3 + 1e-9 * rng.standard_normal(n)  # oldest pair makes O nearly singular
    S2 = S.copy()
    S2[:, 0] = S[:, 1] + 1e-9 * rng.standard_normal(n)
    assert ms.gubarev_window(S2, Y2) >= 1
    assert ms.gubarev_window(S, Y, M=4) == 2
    H = lambda V: V / 50.0
    B = lambda V: 50.0 * V
    d = ms.gubarev_window(S, Y, H=H, B=B)
    assert 0 <= d <= 5


# ----------------------------------------------------------------------------------- runs
@pytest.mark.parametrize(
    "M,exact", [(0, False), (1, False), (2, False), (8, False), (2, True), (8, True)]
)
def test_convergence_quadratic(M, exact):
    prob = Quad(20, 1e3, seed=0)
    g0 = np.linalg.norm(prob.grad(prob.x0))
    r = run_method(
        ms.solve, prob, prob.x0, dict(m=8, M=M, exact_last=exact), budget=5000, gtol=1e-8 * g0
    )
    assert r["status"] == "converged", r["status"]
    assert r["best_gn"] <= 1e-8 * g0


def test_secant_equations_on_quadratic():
    prob = Quad(20, 1e3, seed=1)
    g0 = np.linalg.norm(prob.grad(prob.x0))
    O = Oracle(prob, budget=5000, gtol=1e-8 * g0)
    seen = {"q": [], "checked": 0}

    def cb(ap, x):
        q = ap.last_window
        S, Y = ap.S[:, -q:], ap.Y[:, -q:]
        assert np.allclose(Y, prob.A @ S, rtol=0, atol=1e-8 * np.abs(Y).max()) or ap.n_damped > 0
        if ap.n_damped == 0:
            HY = ap.H(Y)
            assert np.allclose(HY, S, atol=1e-7 * np.abs(S).max())  # H Y_q = S_q (exact data)
            seen["checked"] += 1
        seen["q"].append(q)

    with pytest.raises(Converged):
        ms.solve(O, prob.x0, m=8, M=8, exact_last=False, callback=cb)
    assert seen["checked"] >= 10
    assert max(seen["q"]) == 8  # multi-secant windows are used


@pytest.mark.parametrize("M,exact", [(1, False), (2, False), (8, False), (8, True)])
def test_convergence_rosenbrock(M, exact):
    prob = Rosenbrock(10)
    r = run_method(
        ms.solve, prob, prob.x0, dict(m=8, M=M, exact_last=exact), budget=5000, gtol=1e-6
    )
    assert r["status"] == "converged", r["status"]


class _InfNormOracle(Oracle):
    """Stopping rule (47) of [G26]: ||g||_inf <= min(max(eps_g max(1, ||g0||_inf), eps_g_min), eps_g_max)."""

    def __init__(self, prob, tol, **kw):
        super().__init__(prob, **kw)
        self.tol_inf = tol

    def _update(self, x, fx=None, gx=None):
        super()._update(x, fx, gx)
        if gx is not None and np.max(np.abs(gx)) <= self.tol_inf:
            self.status = "converged"
            raise Converged()


class _DiagQ:
    def __init__(self, n, kappa, seed):
        rng = np.random.default_rng(seed)
        self.lam = rng.uniform(1.0, kappa, n)
        self.n = n
        self.x0 = np.ones(n)
        self.fstar = 0.0

    def f(self, x):
        return 0.5 * float(np.dot(self.lam * x, x))

    def grad(self, x):
        return self.lam * x


def test_paper_claim_random_diagonal_quadratics():
    """[G26] Sec. 5.1 / Fig. 2: M <= L/2 ~ L-BFGS-B; M = L = 8 needs clearly fewer gradients."""
    from scipy.optimize import minimize

    n, kappa = 3000, 1e6
    counts = {1: [], 4: [], 8: []}
    lbfgsb = []
    for seed in range(2):
        prob = _DiagQ(n, kappa, seed)
        g0 = np.max(np.abs(prob.grad(prob.x0)))
        tol = min(max(1e-8 * max(1.0, g0), 1e-4), 1.0)  # (47) with the paper's defaults
        for M in counts:
            O = _InfNormOracle(prob, tol, budget=20000)
            with pytest.raises(Converged):
                ms.solve(O, prob.x0, m=8, M=M)
            counts[M].append(O.n_g)
        nfev = [0]

        def fg(x):
            nfev[0] += 1
            return prob.f(x), prob.grad(x)

        minimize(
            fg,
            prob.x0,
            jac=True,
            method="L-BFGS-B",
            options=dict(maxcor=8, gtol=tol, ftol=0.0, maxiter=20000, maxfun=20000),
        )
        lbfgsb.append(nfev[0])
    c1, c4, c8, cb = (np.mean(counts[1]), np.mean(counts[4]), np.mean(counts[8]), np.mean(lbfgsb))
    assert abs(c1 - cb) <= 0.15 * cb  # single secant ~ L-BFGS-B
    assert abs(c4 - cb) <= 0.15 * cb  # M <= L/2 ~ L-BFGS-B
    assert c8 <= 0.9 * cb and c8 <= 0.9 * c1  # M = L clearly better (paper: factor 0.8 - 0.6)
