"""Tests for methods/lmss.py (L-MSS, Burdakov 1983 / BMP 2002 / Erway-Rezapour 2021)."""

import numpy as np
import pytest

from xrbench.methods import lmss  # noqa: E402
from xrbench.oracle import run_method  # noqa: E402


class Quad:
    def __init__(self, n=20, kappa=1e3, seed=0):
        r = np.random.default_rng(seed)
        Q, _ = np.linalg.qr(r.standard_normal((n, n)))
        self.A = Q @ np.diag(np.geomspace(1.0, kappa, n)) @ Q.T
        self.b = r.standard_normal(n)
        self.n = n
        self.x0 = r.standard_normal(n)
        self.name = f"quad{n}"
        self.err_from_f = True

    def f(self, x):
        return float(0.5 * x @ self.A @ x - self.b @ x)

    def grad(self, x):
        return self.A @ x - self.b


def _pairs(n, p, seed, spd=True):
    """Secant pairs y_i = A_i s_i with different SPD A_i (a non-quadratic 'Hessian history'), oldest first."""
    r = np.random.default_rng(seed)
    S = r.standard_normal((n, p))
    cols = []
    for i in range(p):
        M = r.standard_normal((n, n))
        A = M @ M.T + n * np.eye(n) if spd else M + M.T
        cols.append(A @ S[:, i])
    return S, np.column_stack(cols)


def _recursion(B0, S, Y):
    """MSS rank-two recursion with the least-change c_k = (I - P_{k-1}) s_k  ([BMP] (14)-(16), (22))."""
    B = B0.copy()
    for k in range(S.shape[1]):
        s, y = S[:, k], Y[:, k]
        c = s.copy()
        if k:
            Q, _ = np.linalg.qr(S[:, :k])
            c = c - Q @ (Q.T @ c)
        rr = y - B @ s
        sc = s @ c
        B = B + (np.outer(rr, c) + np.outer(c, rr)) / sc - (rr @ s) * np.outer(c, c) / sc**2
    return B


@pytest.mark.parametrize("seed", [0, 1, 2])
@pytest.mark.parametrize("zeta,zc", [(1.7, 1.7), (2.5, 0.4)])
def test_mss_identities(seed, zeta, zc):
    """S^T B S = Tbar (upper triangle of S^T Y mirrored, oldest first) and B s_new = y_new ([B83] (2.7), (2.11);
    [ER] Lemma 1), for the eigen form with scalar and dense ([ER] (17)) initial matrices."""
    n, p = 15, 6
    S, Y = _pairs(n, p, seed)
    M = S.T @ Y
    T = np.triu(M) + np.triu(M, 1).T
    assert np.allclose(lmss.tbar(S, Y), T)
    P, lam, z = lmss.mss_eig(S, Y, zeta, zc)
    B = lmss.mss_dense_from_eig(P, lam, z)
    sc = np.abs(T).max()
    assert np.abs(B - B.T).max() <= 1e-12 * np.abs(B).max()
    assert np.abs(S.T @ B @ S - T).max() <= 1e-11 * sc
    assert np.linalg.norm(B @ S[:, -1] - Y[:, -1]) <= 1e-11 * np.linalg.norm(Y[:, -1])
    # the oldest secant equation does NOT hold in general (only its projections onto older steps)
    assert np.linalg.norm(B @ S[:, 0] - Y[:, 0]) > 1e-6 * np.linalg.norm(Y[:, 0])
    # S^T (Y - B S) = strictly lower part of S^T Y - Y^T S  (projected secant equations [B83] (2.11))
    D = M - M.T
    assert np.abs(S.T @ (Y - B @ S) - np.tril(D, -1)).max() <= 1e-11 * sc
    if zeta == zc:
        # eigen form = compact form [ER] (8) = least-change recursion [BMP] (14)-(16), (22)
        Bc = lmss.mss_compact(S, Y, zeta * np.eye(n))
        Br = _recursion(zeta * np.eye(n), S, Y)
        assert np.abs(Bc - B).max() <= 1e-11 * np.abs(B).max()
        assert np.abs(Br - B).max() <= 1e-10 * np.abs(B).max()
    else:
        # complement of span[S, Y] has eigenvalue zc
        u = np.random.default_rng(seed).standard_normal(n)
        u -= P @ (P.T @ u)
        assert np.linalg.norm(B @ u - zc * u) <= 1e-11 * np.linalg.norm(u) * max(1, zc)


def test_mss_full_window_quadratic():
    """On quadratic data with n independent steps, S^T B S = S^T A S determines B = A (full-memory MSS)."""
    n = 8
    r = np.random.default_rng(3)
    M = r.standard_normal((n, n))
    A = M @ M.T + np.eye(n)
    S = r.standard_normal((n, n))
    P, lam, z = lmss.mss_eig(S, A @ S, 2.0)
    B = lmss.mss_dense_from_eig(P, lam, z)
    assert np.abs(B - A).max() <= 1e-9 * np.abs(A).max()


def test_select_pairs_sigma_regular():
    """Newest pair always kept; a dependent older pair is skipped ([BMP] (27))."""
    r = np.random.default_rng(0)
    s1, s2 = r.standard_normal(10), r.standard_normal(10)
    Sl = [s1, s2, s1 + 1e-6 * r.standard_normal(10), r.standard_normal(10)]
    idx = lmss.select_pairs(Sl, 0.01, 10)
    assert 3 in idx and 2 in idx and 0 not in idx and 1 in idx
    assert lmss.select_pairs(Sl, 0.01, 2) == [2, 3]


@pytest.mark.parametrize("seed", range(40))
def test_tr_subproblem_optimality(seed):
    """l2 TR subproblem in the eigenbasis satisfies [ER] Thm 1 (12), including indefinite and hard cases."""
    r = np.random.default_rng(seed)
    n = int(r.integers(4, 9))
    p = int(r.integers(1, min(4, n)))
    S, Y = r.standard_normal((n, p)), r.standard_normal((n, p))  # arbitrary pairs: B indefinite
    P, lam, zc = lmss.mss_eig(S, Y, r.uniform(0.1, 3), r.uniform(0.1, 3))
    B = lmss.mss_dense_from_eig(P, lam, zc)
    w, V = np.linalg.eigh(B)
    g = r.standard_normal(n)
    if seed % 4 == 0 and w[0] < 0:
        g -= V[:, 0] * (V[:, 0] @ g)  # hard-case candidate
    delta = 10 ** r.uniform(-2, 1)
    p_, sig, pBp = lmss.tr_subproblem(g, P, lam, zc, delta)
    assert sig >= 0
    assert np.linalg.norm(p_) <= delta * (1 + 1e-9)
    assert w[0] + sig >= -1e-9 * max(1.0, abs(w[0]))
    assert np.linalg.norm((B + sig * np.eye(n)) @ p_ + g) <= 1e-8 * np.linalg.norm(g)
    assert abs(sig * (delta - np.linalg.norm(p_))) <= 1e-8 * (1 + sig) * delta
    assert abs(pBp - p_ @ B @ p_) <= 1e-9 * (1 + abs(pBp))


@pytest.mark.parametrize(
    "params",
    [
        dict(m=10, mode="ls"),
        dict(m=20, mode="ls"),
        dict(m="n", mode="ls"),
        dict(m=10, mode="tr"),
        dict(m=3, mode="tr"),
        dict(m=10, mode="ls", fallback="abs"),
    ],
)
def test_convergence_quadratic(params):
    prob = Quad(20, 1e3, 0)
    g0 = np.linalg.norm(prob.grad(prob.x0))
    res = run_method(lmss.solve, prob, prob.x0, params, budget=5000, gtol=1e-8 * g0)
    assert res["status"] == "converged", res["status"]


def test_full_memory_quadratic_fast():
    """Full-memory MSS: once n independent pairs are stored, B = A and the next unit step is exact."""
    prob = Quad(20, 1e3, 0)
    g0 = np.linalg.norm(prob.grad(prob.x0))
    res = run_method(lmss.solve, prob, prob.x0, dict(m="n"), budget=5000, gtol=1e-8 * g0)
    assert res["status"] == "converged" and res["n_pts"] <= 3 * prob.n
