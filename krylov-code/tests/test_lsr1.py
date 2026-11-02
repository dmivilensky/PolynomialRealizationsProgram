"""Tests for methods/lsr1.py (L-SR1 trust region: Byrd-Nocedal-Schnabel 1994, Byrd-Khalfan-Schnabel 1996,
Nocedal-Wright Alg. 6.2, Brust-Erway-Marcia 2017).

Identities checked:
  * compact form [BNS] Thm 5.1 / [BEM] (4) == dense SR1 recursion (NW (6.24)), with and without skipped pairs;
    eigen form [BEM] (7) == compact form; complement eigenvalue gamma;
  * hereditary secant equations B s_i = y_i for every stored pair on quadratic data (NW Thm 6.1);
  * n linearly independent steps on a quadratic: B = A (NW Thm 6.1, finite termination of the matrix);
  * l2 subproblem optimality conditions (B + sigma I) p = -g, B + sigma I psd, sigma (Delta - ||p||) = 0 on L-SR1
    matrices (indefinite and hard case);
  * convergence: convex quadratic n = 20, kappa = 1e3 to ||g|| <= 1e-8 ||g0||; Rosenbrock n = 10;
  * full memory (m = n) on the quadratic: finite termination in n + 2 points (rejected trials store exact pairs).
"""

import numpy as np
import pytest
from _base1_probs import Rosenbrock
from _infra import Quad, run_gtol

from xrbench.methods import lsr1


def _pairs(n, p, seed, spd=True):
    """Pairs y_i = A_i s_i with different matrices A_i (non-quadratic data), oldest first."""
    r = np.random.default_rng(seed)
    S = r.standard_normal((n, p))
    cols = []
    for i in range(p):
        M = r.standard_normal((n, n))
        A = M @ M.T + n * np.eye(n) if spd else M + M.T
        cols.append(A @ S[:, i])
    return S, np.column_stack(cols)


@pytest.mark.parametrize("seed", range(5))
@pytest.mark.parametrize("gamma", [0.3, 2.0, 40.0])
def test_compact_equals_recursion(seed, gamma):
    n, p = 12, 6
    S, Y = _pairs(n, p, seed, spd=(seed % 2 == 0))
    Bd, kept = lsr1.sr1_dense(S, Y, gamma)
    assert kept == lsr1.sr1_select(S, Y, gamma)
    Bc = lsr1.sr1_compact(S[:, kept], Y[:, kept], gamma)
    sc = np.abs(Bd).max()
    assert np.abs(Bc - Bd).max() <= 1e-10 * sc
    P, lam = lsr1.sr1_eig(S[:, kept], Y[:, kept], gamma)
    Be = lsr1.eig_dense(P, lam, gamma)
    assert np.abs(Be - Bd).max() <= 1e-10 * sc
    u = np.random.default_rng(seed).standard_normal(n)
    u -= P @ (P.T @ u)
    assert np.linalg.norm(Be @ u - gamma * u) <= 1e-10 * np.linalg.norm(u) * max(1.0, gamma)
    v = np.random.default_rng(seed + 7).standard_normal(n)
    assert np.allclose(
        lsr1.apply_B(P, lam, gamma, v), Bd @ v, rtol=1e-10, atol=1e-10 * sc * np.linalg.norm(v)
    )


def test_skipping_rule_drops_a_degenerate_pair():
    """A pair with y - B s (nearly) orthogonal to s, |s^T (y - B s)| < r ||s|| ||y - B s||, is skipped (NW (6.26)),
    in the recursion and in the compact selection alike; the later pairs are still used."""
    n, gamma = 10, 1.5
    S, Y = _pairs(n, 3, 4)
    B2, _ = lsr1.sr1_dense(S[:, :2], Y[:, :2], gamma)
    rng = np.random.default_rng(9)
    s3, w = rng.standard_normal(n), rng.standard_normal(n)
    v = w - (w @ s3) / (s3 @ s3) * s3  # v orthogonal to s3
    v += (
        1e-12 * np.linalg.norm(v) * s3 / np.linalg.norm(s3)
    )  # |s^T v| = 1e-12 ||s|| ||v|| < 1e-8 ||s|| ||v||
    S2 = np.column_stack([S[:, :2], s3, S[:, 2]])
    Y2 = np.column_stack([Y[:, :2], B2 @ s3 + v, Y[:, 2]])
    kept = lsr1.sr1_select(S2, Y2, gamma)
    assert kept == [0, 1, 3]
    Bd, kd = lsr1.sr1_dense(S2, Y2, gamma)
    assert kd == kept
    assert (
        np.abs(lsr1.sr1_compact(S2[:, kept], Y2[:, kept], gamma) - Bd).max()
        <= 1e-10 * np.abs(Bd).max()
    )


@pytest.mark.parametrize("seed", range(4))
@pytest.mark.parametrize("gamma", [0.5, 3.0, 1e3])
def test_hereditary_secant_quadratic(seed, gamma):
    """On quadratic data y_i = A s_i the SR1 matrix satisfies B s_i = y_i for every stored pair (NW Thm 6.1)."""
    n, p = 15, 7
    r = np.random.default_rng(seed)
    M = r.standard_normal((n, n))
    A = M @ M.T + np.eye(n) if seed % 2 == 0 else M + M.T  # also indefinite A
    S = r.standard_normal((n, p))
    Y = A @ S
    kept = lsr1.sr1_select(S, Y, gamma)
    assert kept == list(range(p))
    P, lam = lsr1.sr1_eig(S, Y, gamma)
    B = lsr1.eig_dense(P, lam, gamma)
    assert np.abs(B @ S - Y).max() <= 1e-9 * np.abs(Y).max()


def test_quadratic_full_rank_gives_A():
    """n linearly independent steps on a quadratic: the SR1 matrix equals A (gamma not an eigenvalue of A)."""
    n = 9
    r = np.random.default_rng(3)
    M = r.standard_normal((n, n))
    A = M @ M.T + np.eye(n)
    S = r.standard_normal((n, n))
    Bd, kept = lsr1.sr1_dense(S, A @ S, 0.7)
    assert kept == list(range(n))
    assert np.abs(Bd - A).max() <= 1e-8 * np.abs(A).max()
    P, lam = lsr1.sr1_eig(S, A @ S, 0.7)
    assert np.abs(lsr1.eig_dense(P, lam, 0.7) - A).max() <= 1e-8 * np.abs(A).max()


@pytest.mark.parametrize("seed", range(200))
def test_subproblem_optimality(seed):
    """OBS solution on L-SR1 matrices: optimality conditions of the l2 subproblem (Brust et al. 2017, (5))."""
    r = np.random.default_rng(seed)
    n = int(r.integers(5, 10))
    p = int(r.integers(1, min(5, n)))
    S, Y = r.standard_normal((n, p)), r.standard_normal((n, p))  # arbitrary pairs: B indefinite
    gamma = r.uniform(0.1, 3.0)
    kept = lsr1.sr1_select(S, Y, gamma)
    P, lam = lsr1.sr1_eig(S[:, kept], Y[:, kept], gamma)
    B = lsr1.eig_dense(P, lam, gamma)
    w, V = np.linalg.eigh(B)
    g = r.standard_normal(n)
    if seed % 4 == 0 and w[0] < 0:
        g -= V[:, 0] * (V[:, 0] @ g)  # hard-case candidate
    delta = 10 ** r.uniform(-2, 1)
    pp, sig, pBp = lsr1.obs_subproblem(g, P, lam, gamma, delta)
    assert sig >= 0
    assert np.linalg.norm(pp) <= delta * (1 + 1e-9)
    assert w[0] + sig >= -1e-9 * max(1.0, abs(w[0]))
    assert np.linalg.norm((B + sig * np.eye(n)) @ pp + g) <= 1e-8 * np.linalg.norm(g)
    assert abs(sig * (delta - np.linalg.norm(pp))) <= 1e-8 * (1 + sig) * delta
    assert abs(pBp - pp @ B @ pp) <= 1e-9 * (1 + abs(pBp))


@pytest.mark.parametrize(
    "params", [dict(m=5), dict(m=10), dict(m=5, gamma="sy"), dict(m=10, gamma="egmo")]
)
def test_convergence_quadratic(params):
    res = run_gtol(lsr1.solve, Quad(20, 1e3, 0), params, budget=20000)
    assert res["status"] == "converged", res["status"]


@pytest.mark.parametrize("m", [5, 10])
def test_convergence_rosenbrock(m):
    P = Rosenbrock(10)
    res = run_gtol(lsr1.solve, P, dict(m=m), budget=20000)
    assert res["status"] == "converged", res["status"]
    assert res["best_f"] <= 1e-10


def test_updates_at_rejected_steps(monkeypatch):
    """The pair of every trial, accepted or rejected, enters the memory (BKS 1996; NW Alg. 6.2): the newest column of
    the next model is the previous trial step, at every iteration, and rejections do occur."""
    steps, newest = [], []
    orig_tr, orig_eig = lsr1.obs_subproblem, lsr1.sr1_eig

    def tr(g, P, lam, gam, delta):
        out = orig_tr(g, P, lam, gam, delta)
        steps.append(out[0].copy())
        return out

    def eig(S, Y, gam, *a, **k):
        newest.append((len(steps), S[:, -1].copy()))
        return orig_eig(S, Y, gam, *a, **k)

    monkeypatch.setattr(lsr1, "obs_subproblem", tr)
    monkeypatch.setattr(lsr1, "sr1_eig", eig)
    res = run_gtol(lsr1.solve, Rosenbrock(10), dict(m=5), budget=20000)
    assert res["info"]["counters"]["nrej"] > 0 and res["info"]["counters"]["nskip"] == 0
    assert len(newest) == len(steps) - 1
    for k, s in newest:
        p = steps[k - 1]
        assert np.linalg.norm(s / np.linalg.norm(s) - p / np.linalg.norm(p)) <= 1e-12


@pytest.mark.parametrize("gamma", ["yy", "sy", "egmo"])
def test_full_memory_finite_termination(gamma):
    """Memory m >= n on a quadratic: every trial (accepted or rejected) gives an exact pair y = A s; after n linearly
    independent pairs B = A (NW Thm 6.1) and the next step is the exact minimizer: n + 2 points in total here."""
    P = Quad(20, 1e3, 0)
    res = run_gtol(lsr1.solve, P, dict(m=20, gamma=gamma), budget=1000)
    assert res["status"] == "converged" and res["n_pts"] <= P.n + 2
