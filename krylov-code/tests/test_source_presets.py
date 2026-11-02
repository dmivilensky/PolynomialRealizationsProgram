"""Independent checks for the published SC-INF presets and stable O-ACCEL."""

import numpy as np
import pytest

from xrbench.methods import lmss, lsr1
from xrbench.methods._trust_region import shape_infinity_subproblem, shape_norm
from xrbench.oracle import run_method


@pytest.mark.parametrize("seed", range(24))
def test_shape_infinity_global_minimum(seed):
    """Independent scalar/ball solutions check indefinite and hard cases."""
    rng = np.random.default_rng(seed)
    n = 8
    r = seed % (n + 1)
    P = np.linalg.qr(rng.standard_normal((n, n)))[0][:, :r]
    lam = rng.uniform(-4.0, 4.0, r)
    gamma = [-1.0, 0.0, 2.0][seed % 3]
    delta = 10.0 ** rng.uniform(-1.0, 1.0)
    g = rng.normal(size=n)
    if seed % 4 == 0:
        g = np.zeros(n)  # negative-curvature hard cases in either subspace
    p, pBp = shape_infinity_subproblem(g, P, lam, gamma, delta)
    a = P.T @ g
    v = P.T @ p
    perp = p - P @ v
    gp = g - P @ a
    assert shape_norm(p, P) <= delta * (1.0 + 1e-12)
    expected = 0.0
    for ai, li in zip(a, lam):
        candidates = [-delta, 0.0, delta]
        if li > 0 and abs(ai / li) <= delta:
            candidates.append(-ai / li)
        expected += min(ai * t + 0.5 * li * t * t for t in candidates)
    ng = np.linalg.norm(gp)
    if r < n:
        radius = min(ng / gamma, delta) if gamma > 0 else delta
        expected += -ng * radius + 0.5 * gamma * radius * radius
    assert np.isclose(g @ p + 0.5 * pBp, expected, rtol=1e-11, atol=1e-11)
    assert np.isclose(pBp, np.dot(lam, v * v) + gamma * (perp @ perp), rtol=1e-11, atol=1e-11)


class Quadratic:
    def __init__(self):
        rng = np.random.default_rng(37)
        self.n = 20
        Q = np.linalg.qr(rng.normal(size=(self.n, self.n)))[0]
        self.A = Q @ np.diag(np.geomspace(1, 1000, self.n)) @ Q.T
        self.x0 = rng.normal(size=self.n)
        self.name = "source-preset-quadratic"

    def f(self, x):
        return 0.5 * x @ self.A @ x

    def grad(self, x):
        return self.A @ x


@pytest.mark.parametrize(
    "solver,params",
    [
        (lmss.solve, dict(m=3, q=5, mode="tr", init="dense", tr_norm="linf")),
        (lsr1.solve, dict(m=5, q=7, gamma="max", tr_norm="linf")),
    ],
)
def test_published_shape_presets_converge(solver, params):
    problem = Quadratic()
    tolerance = 1e-8 * np.linalg.norm(problem.grad(problem.x0))
    result = run_method(solver, problem, problem.x0, params, budget=5000, gtol=tolerance)
    assert result["status"] == "converged", result
    assert result["best_gn"] <= tolerance


def test_native_lbfgs_direction_matches_verified_two_loop():
    """Native directions agree with Methods/LBFGS.lean on the same real pairs.

    Compare directions from compiled SciPy with an independent dense inverse
    BFGS recursion. This checks pair order, scalar initialization and update
    convention without substituting an exact line search for the native one.
    """
    from xrbench.methods import lbfgs_scipy

    problem = Quadratic()

    class TraceOracle:
        def __init__(self):
            self.accepted = []
            self.probes = []
            self.last = None

        def fg(self, x):
            x = np.array(x, copy=True)
            g = problem.grad(x)
            self.probes.append((len(self.accepted), x))
            self.last = (x, g)
            return problem.f(x), g

        def mark_iter(self):
            self.accepted.append(self.last)
            if len(self.accepted) == 5:
                raise StopIteration

        def note(self, key, value):
            pass

    oracle = TraceOracle()
    memory = 3
    lbfgs_scipy.solve(oracle, problem.x0, m=memory)
    states = [(problem.x0, problem.grad(problem.x0)), *oracle.accepted]
    for k in range(1, 5):
        x, _ = states[k]
        stored = []
        for j in range(max(0, k - memory), k):
            s = states[j + 1][0] - states[j][0]
            y = states[j + 1][1] - states[j][1]
            stored.append((s, y))
        s, y = stored[-1]
        H = (s @ y) / (y @ y) * np.eye(problem.n)
        for s, y in stored:  # chronological dense BFGS, independent of two-loop code
            rho = 1.0 / (s @ y)
            V = np.eye(problem.n) - rho * np.outer(s, y)
            H = V @ H @ V.T + rho * np.outer(s, s)
        expected = -H @ states[k][1]
        probe = next(point for iteration, point in oracle.probes if iteration == k)
        measured = probe - x
        # Unit native first trial after the first iteration.
        assert np.allclose(measured, expected, rtol=2e-11, atol=2e-12)


def test_cutest_adapter_keeps_function_trials_gradient_free():
    """Exercise the real CUTEst adapter against a counted native backend API."""
    from xrbench.oracle import Oracle
    from xrbench.problems.cutest import CutestProblem

    class NativeBackend:
        def __init__(self):
            self.f_calls = self.g_calls = self.fg_calls = 0

        def obj(self, x, gradient=False):
            f = float(x @ x)
            if gradient:
                self.fg_calls += 1
                return f, 2 * x
            self.f_calls += 1
            return f

        def grad(self, x):
            self.g_calls += 1
            return 2 * x

    # The adapter methods are tested directly; optional native installation and
    # SIF decoding are irrelevant to this accounting contract.
    problem = object.__new__(CutestProblem)
    problem.p = NativeBackend()
    oracle = Oracle(problem)
    x = np.ones(3)
    oracle.f(x)
    assert (problem.p.f_calls, problem.p.g_calls, problem.p.fg_calls) == (1, 0, 0)
    oracle.g(x)
    oracle.fg(x)  # central cache: no repeated native computation
    oracle.fg(x + 1)
    assert (problem.p.f_calls, problem.p.g_calls, problem.p.fg_calls) == (1, 1, 1)
    assert (oracle.n_f_evals, oracle.n_g_evals, oracle.n_fg_evals) == (2, 2, 1)
    assert oracle.n_pts == 2
