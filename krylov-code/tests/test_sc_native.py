"""SC C loops checked against dense mathematics and source-aligned reference.

The compact matrices and subproblem are the production C functions. Dense
reconstructions avoid requiring a second implementation to make the same
factorization choices. Original source audit: docs/NativeSCAudit.md.
"""
import numpy as np
import pytest
from test_lmss import Quad

from xrbench.methods import lmss, lsr1
from xrbench.methods.competitors_native import solve
from xrbench.native.competitor_build import load_native
from xrbench.oracle import run_method


def model(S, Y, variant, gamma, gc):
    native = load_native()
    n = S.shape[0]
    P, lam, rank = native.sc_model(S.ravel(order="F"), Y.ravel(order="F"), n, variant, gamma, gc)
    return np.asarray(P).reshape((n, rank), order="F"), np.asarray(lam)


def step(g, P, lam, gc, delta):
    p, pBp = load_native().sc_step(g, P.ravel(order="F"), lam, g.size, lam.size, gc, delta)
    return np.asarray(p), pBp


@pytest.mark.parametrize("variant", [0, 1])
@pytest.mark.parametrize("seed", range(12))
def test_model_independent_dense_recursion(variant, seed):
    rng = np.random.default_rng(seed)
    n, m = 14, 4
    S, Y = rng.normal(size=(2, n, m))
    gamma, gc = 2.3, .7 if variant == 0 else 2.3
    P, lam = model(S, Y, variant, gamma, gc)
    B = P @ np.diag(lam - gc) @ P.T + gc * np.eye(n)
    if variant:
        # Dense SR1 recursion uses every supplied nondegenerate pair.
        expected, kept = lsr1.sr1_dense(S, Y, gamma, r=0)
        assert len(kept) == m
    else:
        # Independent least-change MSS rank-two recursion.
        Q = np.linalg.qr(np.column_stack((S, Y)))[0]
        expected = gamma * (Q @ Q.T) + gc * (np.eye(n) - Q @ Q.T)
        for j in range(m):
            s, y = S[:, j], Y[:, j]
            c = s.copy()
            if j:
                QS = np.linalg.qr(S[:, :j])[0]
                c -= QS @ (QS.T @ c)
            v = y - expected @ s
            expected += (np.outer(v, c) + np.outer(c, v)) / (s @ c) - (s @ v) * np.outer(c, c) / (s @ c) ** 2
    np.testing.assert_allclose(B, expected, rtol=2e-9, atol=2e-9 * max(1, np.linalg.norm(expected)))
    np.testing.assert_allclose(P.T @ P, np.eye(lam.size), atol=2e-14)


@pytest.mark.parametrize("variant", [0, 1])
@pytest.mark.parametrize("scale", [1e-8, 1, 1e8])
def test_model_pair_normalization_invariant(variant, scale):
    rng = np.random.default_rng(40)
    S, Y = rng.normal(size=(2, 10, 3))
    P, lam = model(S, Y, variant, 1.4, 1.4)
    P2, lam2 = model(S * scale, Y * scale, variant, 1.4, 1.4)
    np.testing.assert_allclose(P @ np.diag(lam - 1.4) @ P.T, P2 @ np.diag(lam2 - 1.4) @ P2.T, atol=1e-11)


def test_mss_dependent_window_selects_subspace():
    S = np.array([[1., 0, 1], [0, 1, 0], [0, 0, 0], [0, 0, 0]])
    A = np.diag([2., 3, 4, 5])
    P, lam = model(S, A @ S, 0, 1, 1)
    B = P @ np.diag(lam - 1) @ P.T + np.eye(4)
    np.testing.assert_allclose(B, np.diag([2., 3, 1, 1]), atol=2e-14)


@pytest.mark.parametrize("seed", range(20))
def test_shape_step_separable_global_minimum(seed):
    rng = np.random.default_rng(seed)
    n, r = 8, seed % 6
    P = np.linalg.qr(rng.normal(size=(n, r)))[0]
    lam = rng.normal(size=r)
    gamma = rng.uniform(-2, 2)
    g, delta = rng.normal(size=n), .4
    p, pBp = step(g, P, lam, gamma, delta)
    B = P @ np.diag(lam - gamma) @ P.T + gamma * np.eye(n)
    np.testing.assert_allclose(pBp, p @ B @ p, atol=2e-14)
    a = P.T @ g
    gp = g - P @ a
    scalar_min = sum(min(-delta * abs(ai) + .5 * li * delta**2,
                         -.5 * ai**2 / li if li > 0 and abs(ai / li) <= delta else np.inf)
                     for ai, li in zip(a, lam))
    nr = min(delta, np.linalg.norm(gp) / gamma) if gamma > 0 else delta
    exact = scalar_min - np.linalg.norm(gp) * nr + .5 * gamma * nr**2
    np.testing.assert_allclose(g @ p + .5 * pBp, exact, atol=2e-14)
    assert max(np.max(np.abs(P.T @ p), initial=0), np.linalg.norm(p - P @ (P.T @ p))) <= delta * (1 + 1e-13)


def test_negative_complement_zero_gradient_hard_case():
    P = np.eye(5)[:, :2].copy()
    g = np.zeros(5)
    p, pBp = step(g, P, np.array([1., 2]), -3., .25)
    assert abs(np.linalg.norm(p) - .25) < 1e-15
    assert abs(pBp + 3 * .25**2) < 1e-15


@pytest.mark.parametrize("method", ["mss", "sr1"])
@pytest.mark.parametrize("n,kappa", [(5, 10), (20, 100), (35, 1000)])
def test_full_loop_quadratic(method, n, kappa):
    prob = Quad(n, kappa, 3)
    params = dict(native_method=method, m=3 if method == "mss" else 5, q=5 if method == "mss" else 7)
    result = run_method(solve, prob, prob.x0, params, budget=10000, relative_gtol=1e-8)
    assert result["status"] == "converged", result


class _FixedTrials:
    """Small exact diagonal quadratic, stop after a fixed callback sequence."""
    def __init__(self, limit=9):
        self.points = []
        self.limit = limit
        self.notes = {}
    def fg(self, x):
        if len(self.points) >= self.limit:
            raise _End
        self.points.append(x.copy())
        a = np.arange(1, x.size + 1, dtype=float)
        return .5 * np.dot(a * x, x), a * x
    def f(self, x):
        return self.fg(x)[0]
    def g(self, x):
        return self.fg(x)[1]
    def mark_iter(self):
        pass
    def note(self, key, value):
        self.notes[key] = value


class _End(Exception):
    pass


@pytest.mark.parametrize("method", ["mss", "sr1"])
def test_complete_trial_sequence_matches_source_aligned_python(method):
    a, b = _FixedTrials(), _FixedTrials()
    x0 = np.arange(1., 9)
    reference = lmss._solve_shape if method == "mss" else lsr1._solve_shape
    with pytest.raises(_End):
        reference(a, x0)
    with pytest.raises(_End):
        solve(b, x0, native_method=method)
    np.testing.assert_allclose(b.points, a.points, rtol=2e-8, atol=2e-9)
    assert len(a.points) == len(b.points)
    assert "nrej" in b.notes and "nskip" in b.notes


@pytest.mark.parametrize("method", ["mss", "sr1"])
def test_native_callback_error_preserved(method):
    class Sentinel(Exception):
        pass
    class Broken(_FixedTrials):
        def fg(self, x):
            raise Sentinel("original callback")
    with pytest.raises(Sentinel, match="original callback"):
        solve(Broken(), np.ones(3), native_method=method)


@pytest.mark.parametrize("method", ["mss", "sr1"])
def test_author_first_model_fixture(method):
    """Reconstruct the first compact model from author initialization equations.

    This uses only the initial accepted observation and a dense rank update;
    neither the Python spectral model nor C model diagnostic supplies B.
    """
    oracle, trace = _FixedTrials(5), []
    x0 = np.arange(1., 9)
    with pytest.raises(_End):
        solve(oracle, x0, native_method=method, trace=trace)
    event = trace[0]
    # The first MT candidate is rejected; candidate two is the accepted point.
    x1 = oracle.points[2]
    s = x1 - x0
    diagonal = np.arange(1., 9)
    y = diagonal * s
    gamma = max(1., (y @ y) / (s @ y))
    gc = 1. if method == "mss" else gamma
    if method == "sr1":
        v = y - gamma * s
        B = gamma * np.eye(8) + np.outer(v, v) / (s @ v)
    else:
        Q = np.linalg.qr(np.column_stack((s, y)))[0]
        B0 = gamma * (Q @ Q.T) + gc * (np.eye(8) - Q @ Q.T)
        v = y - B0 @ s
        B = B0 + (np.outer(v, s) + np.outer(s, v)) / (s @ s) - (s @ v) * np.outer(s, s) / (s @ s)**2
    trial = event["x"] - x1
    pred = -(diagonal * x1) @ trial - .5 * trial @ B @ trial
    np.testing.assert_allclose(event["gamma"], gamma, rtol=2e-14)
    np.testing.assert_allclose(event["gamma_perp"], gc, rtol=2e-14)
    np.testing.assert_allclose(event["radius"], 2 * np.linalg.norm(s), rtol=2e-14)
    np.testing.assert_allclose(event["predicted_decrease"], pred, rtol=2e-12)
    fx1 = .5 * np.dot(diagonal * x1, x1)
    ftrial = .5 * np.dot(diagonal * event["x"], event["x"])
    np.testing.assert_allclose(event["ratio"], (fx1 - ftrial) / pred, rtol=2e-12)


@pytest.mark.parametrize("method", ["mss", "sr1"])
@pytest.mark.parametrize("seed", [0, 4])
def test_nonlinear_full_loop_and_actual_oracle_accounting(method, seed):
    from xrbench.problems.synthetic import SmoothQuadratic

    prob = SmoothQuadratic(n=20, kappa=100, epsilon=.1, seed=seed)
    result = run_method(solve, prob, prob.x0, {"native_method": method}, budget=10000, relative_gtol=1e-8)
    assert result["status"] == "converged", result
    # Both selected SC variants request fg once at every evaluated trial.
    # A shared cache can service duplicates but never hides actual gradients.
    assert result["n_f_evals"] == result["n_g_evals"]
    assert result["n_f"] == result["n_g_requests"]


@pytest.mark.parametrize("method", ["mss", "sr1"])
def test_current_plus_previous_q_history_on_accepted_and_rejected_trials(method):
    from collections import deque

    oracle, trace = _FixedTrials(11), []
    x0 = np.arange(1., 9)
    with pytest.raises(_End):
        solve(oracle, x0, native_method=method, q=2, trace=trace)
    diagonal = np.arange(1., 9)
    x = oracle.points[2]
    s = x - x0
    y = diagonal * s
    gamma = max(1., (y @ y) / (s @ y))
    history = deque([1., gamma], maxlen=2)
    gc = 1. if method == "mss" else gamma
    for event in trace:
        np.testing.assert_allclose(event["gamma"], gamma, rtol=2e-13)
        np.testing.assert_allclose(event["gamma_perp"], gc, rtol=2e-13)
        s = event["x"] - x
        y = diagonal * s
        bb = (y @ y) / (s @ y)
        gamma = max(*history, bb)
        history.append(bb)
        gc = bb if method == "mss" else gamma
        if event["accepted"]:
            x = event["x"]


@pytest.mark.parametrize("method", ["mss", "sr1"])
def test_author_initial_boundary_warning_keeps_sufficient_decrease_seed(method):
    """Author CVSRCH warning5 still seeds the TR model at stpmax=5.

    This flat positive quadratic cannot meet strong Wolfe for alpha<=5.
    Discarding the returned decreasing boundary point would incorrectly stop
    before building a trust-region model (also seen on CUTEst FLETBV3M).
    """
    class BoundarySeed(_FixedTrials):
        def fg(self, x):
            self.points.append(x.copy())
            return .5e-4 * (x @ x), 1e-4 * x
        def mark_iter(self):
            raise _End

    x0 = np.ones(5)
    reference = lmss._solve_shape if method == "mss" else lsr1._solve_shape
    for executor in (reference, lambda O, x: solve(O, x, native_method=method)):
        oracle = BoundarySeed()
        with pytest.raises(_End):
            executor(oracle, x0)
        assert len(oracle.points) == 3
        expected = (1 - 5e-4) * x0
        np.testing.assert_allclose(oracle.points[-1], expected, rtol=0, atol=2e-16)
        d, g0 = -1e-4 * x0, 1e-4 * x0
        f0, fnew = .5e-4 * (x0 @ x0), .5e-4 * (expected @ expected)
        assert fnew <= f0 + 1e-4 * 5 * (g0 @ d)
        assert abs((1e-4 * expected) @ d) > .9 * abs(g0 @ d)
