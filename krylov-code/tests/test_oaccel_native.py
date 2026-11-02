"""Full-C O-ACCEL: paper identities, reference differential and MT audit."""
import numpy as np
import pytest

from xrbench.methods.competitors_native import solve
from xrbench.methods.oaccel import _more_thuente
from xrbench.methods.oaccel import solve as reference
from xrbench.native.competitor_build import load_native
from xrbench.oracle import run_method


class Problem:
    name = "native-OACCEL-quadratic"
    convex = True
    meta = {}

    def __init__(self, n=12, kappa=30, seed=0, shift=0):
        self.n = n
        rng = np.random.default_rng(seed)
        Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
        self.A = (Q * np.geomspace(1, kappa, n)) @ Q.T
        self.shift = np.full(n, shift)
        self.x0 = self.shift + rng.normal(size=n)

    def fg(self, x):
        y = x - self.shift
        g = self.A @ y
        return 0.5 * y @ g, g

    def f(self, x):
        return self.fg(x)[0]

    def grad(self, x):
        return self.fg(x)[1]


class Recording:
    def __init__(self, problem, max_iters=100):
        self.problem = problem
        self.max_iters = max_iters
        self.points = []
        self.nit = 0
        self.notes = {}

    def fg(self, x):
        self.points.append(x.copy())
        return self.problem.fg(x)

    def f(self, x):
        return self.problem.f(x)

    def g(self, x):
        return self.problem.grad(x)

    def mark_iter(self):
        self.nit += 1
        if self.nit >= self.max_iters:
            raise Halt

    def note(self, key, value):
        self.notes[key] = value


class Halt(Exception):
    pass


@pytest.mark.parametrize("precond", ["A", "B"])
@pytest.mark.parametrize("seed", [0, 3, 7])
def test_native_converges_with_published_preconditioners(precond, seed):
    p = Problem(seed=seed)
    r = run_method(solve, p, p.x0, dict(native_method="oaccel", precond=precond),
                   budget=3000, gtol=1e-7)
    assert r["status"] == "converged"
    assert r["n_g_evals"] <= r["n_g_requests"]
    assert r["n_fg_evals"] <= r["n_g_evals"]
    if precond == "B":
        assert r["n_g"] == r["n_g_evals"] == r["n_fg_evals"]


@pytest.mark.parametrize("precond", ["A", "B"])
def test_early_independent_python_trajectories(precond):
    p = Problem(n=15, kappa=10)
    histories = []
    for fn, extra in [(reference, {}), (solve, {"native_method": "oaccel"})]:
        oracle = Recording(p, max_iters=4)
        trace = []
        with pytest.raises(Halt):
            fn(oracle, p.x0, precond=precond, trace=trace, **extra)
        histories.append((oracle.points, trace))
    assert len(histories[0][0]) == len(histories[1][0])
    np.testing.assert_allclose(histories[0][0], histories[1][0], rtol=2e-7, atol=2e-8)
    for a, b in zip(histories[0][1], histories[1][1], strict=True):
        np.testing.assert_allclose(a["x_A"], b["x_A"], rtol=2e-7, atol=2e-8)
        assert bool(a["restart"]) == bool(b["restart"])


def test_unregularized_quadratic_is_fom():
    p = Problem(n=15, kappa=30)
    oracle = Recording(p, max_iters=6)
    trace = []
    with pytest.raises(Halt):
        solve(oracle, p.x0, native_method="oaccel", eps0=0, wmax=20, trace=trace)
    # Independent dense Galerkin point on K_k(A,g0), orthonormalized afresh.
    g0 = p.grad(p.x0)
    vectors = []
    v = g0.copy()
    for k, t in enumerate(trace, start=1):
        for _ in range(2):
            for q in vectors:
                v -= q @ v * q
        v /= np.linalg.norm(v)
        vectors.append(v.copy())
        V = np.column_stack(vectors)
        expected = p.x0 - V @ np.linalg.solve(V.T @ p.A @ V, V.T @ g0)
        np.testing.assert_allclose(t["x_A"], expected, atol=5e-7, rtol=5e-7)
        v = p.A @ v
        assert t["curw"] == k


@pytest.mark.parametrize("initial", [1e-4, 1.0, 100.0])
@pytest.mark.parametrize("quartic", [0.0, 0.1, 10.0])
def test_more_thuente_matches_independent_scipy_dcstep(initial, quartic):
    class Function:
        @staticmethod
        def fg(x):
            return 0.5 * (x @ x) + quartic * np.sum(x**4), x + 4 * quartic * x**3

    x = np.array([1.0, -0.5])
    f0, g0 = Function.fg(x)
    d = -g0
    old, new = Recording(Function), Recording(Function)
    kw = dict(c1=1e-4, c2=.1, xtol=1e-8, stpmin=1e-16, stpmax=65536., maxfev=20)
    py = _more_thuente(old, x, f0, g0, d, initial, **kw)
    status, xn, fn, gn = load_native().line_search(
        new, x, f0, g0, d, initial, kw["c1"], kw["c2"], kw["xtol"],
        kw["stpmin"], kw["stpmax"], kw["maxfev"], 1,
    )
    assert status == (py is not None)
    assert len(old.points) == len(new.points)
    np.testing.assert_allclose(old.points, new.points, rtol=2e-12, atol=2e-12)
    if py is not None:
        np.testing.assert_allclose(xn, py[1], atol=2e-12)
        np.testing.assert_allclose(gn, py[3], atol=2e-12)
        assert fn == pytest.approx(py[2])


def test_callback_exception_retains_identity():
    p = Problem()
    expected = RuntimeError("oracle exception identity")
    oracle = Recording(p)

    def fail(x):
        raise expected

    oracle.fg = fail
    with pytest.raises(RuntimeError) as error:
        solve(oracle, p.x0, native_method="oaccel")
    assert error.value is expected


def test_nonfinite_preconditioner_halving_is_counted():
    p = Problem()
    oracle = Recording(p, max_iters=1)
    fg_original = oracle.fg
    f_calls = []
    g_calls = []

    def fg(x):
        if oracle.points:
            oracle.points.append(x.copy())
            return np.inf, np.full(p.n, np.nan)
        return fg_original(x)

    def f(x):
        f_calls.append(x.copy())
        return p.f(x)

    def g(x):
        g_calls.append(x.copy())
        return p.grad(x)

    oracle.fg, oracle.f, oracle.g = fg, f, g
    with pytest.raises(Halt):
        solve(oracle, p.x0, native_method="oaccel")
    assert len(f_calls) == len(g_calls) == 1
    np.testing.assert_allclose(f_calls[0], .5 * (oracle.points[1] + p.x0))


def test_more_thuente_warning_fallback_is_explicit_and_optional():
    p = Problem(n=3)
    x = p.x0
    f, g = p.fg(x)
    d = -g
    for fallback in (0, 1):
        oracle = Recording(p)
        status, xn, fn, _ = load_native().line_search(
            oracle, x, f, g, d, 1e-8, 1e-4, .1, 1e-8, 1e-16, 65536., 1, fallback,
        )
        assert len(oracle.points) == 1
        assert status == fallback
        if status:
            np.testing.assert_allclose(xn, x + 1e-8 * d)
            assert fn < f


def test_cached_history_is_stable_under_large_common_translation():
    p = Problem(n=15, kappa=10)
    shifted = Problem(n=15, kappa=10, shift=1e6)
    traces = []
    for problem in (p, shifted):
        tr = []
        with pytest.raises(Halt):
            solve(Recording(problem, max_iters=4), problem.x0,
                  native_method="oaccel", trace=tr)
        traces.append(tr)
    for a, b in zip(*traces, strict=True):
        np.testing.assert_allclose(a["x"], b["x"] - shifted.shift, atol=3e-4, rtol=3e-4)


def test_initial_nonfinite_search_allows_52_halvings_and_counts_every_trial():
    class NarrowDomain:
        @staticmethod
        def fg(x):
            if x[0] < 1 - 2.0**-25:
                return np.inf, np.array([np.nan])
            return x[0], np.ones(1)

    x, g, d = np.ones(1), np.ones(1), -np.ones(1)
    old, new = Recording(NarrowDomain), Recording(NarrowDomain)
    kw = dict(c1=1e-4, c2=.1, xtol=1e-8, stpmin=1e-16, stpmax=65536., maxfev=20)
    py = _more_thuente(old, x, 1., g, d, 1., **kw)
    status, xn, fn, gn = load_native().line_search(
        new, x, 1., g, d, 1., 1e-4, .1, 1e-8, 1e-16, 65536., 20, 1,
    )
    assert status == 1
    assert len(old.points) == len(new.points) == 26
    np.testing.assert_array_equal(old.points, new.points)
    np.testing.assert_array_equal(xn, py[1])
    assert fn == py[2]
    np.testing.assert_array_equal(gn, py[3])
