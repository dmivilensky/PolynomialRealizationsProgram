"""Independent checks against the current article and exact-real Lean definitions."""

import numpy as np
import pytest
from _infra import Quad, cg_iterates, run_gtol
from scipy.linalg import eigvalsh

from xrbench.methods import xr
from xrbench.methods._xr_model import (
    consistency_interval,
    unrefuted_suffix,
    update_capacity,
    value_model,
)


def state_from_pairs(S, Y, gradient=None, capacity=None):
    n, p = S.shape
    state = xr.State(
        np.zeros(n),
        0.0,
        np.arange(1.0, n + 1) if gradient is None else gradient,
        p if capacity is None else capacity,
        1.0,
        1e-10,
        1e10,
    )
    state.pairs = [xr.Pair.observe(S[:, j], Y[:, j]) for j in range(p)]
    assert all(pair is not None for pair in state.pairs)
    return state


@pytest.mark.parametrize("seed", range(8))
def test_reverse_cholesky_returns_longest_hermitian_positive_suffix(seed):
    rng = np.random.default_rng(seed)
    C = rng.normal(size=(7, 7))
    np.fill_diagonal(C, rng.uniform(0.5, 3.0, 7))
    for theta in (0.5, 1.0, 2.0):
        feasible = [
            j
            for j in range(7)
            if np.linalg.eigvalsh(xr.latest(C[j:, j:]) + 1j * (C[j:, j:] - C[j:, j:].T) / theta)[0]
            > 0
        ]
        assert unrefuted_suffix(C, theta) == min(feasible)
        scale = np.diag(rng.uniform(0.1, 10, 7) * rng.choice([-1, 1], 7))
        assert unrefuted_suffix(scale @ C @ scale, theta) == min(feasible)


def test_rank_cleanup_keeps_longest_independent_chronological_suffix():
    S = np.array([[1.0, 0.0, 1.0], [0.0, 1.0, 0.0], [0.0, 0.0, 0.0]])
    state = state_from_pairs(S, 2 * S)
    result = xr.model_step(state, xr.Parameters(m0=3, m_max=3))
    assert result.first_pairs == 2 and result.deleted == 0
    assert state.counters["nrank_deleted"] == 1
    np.testing.assert_array_equal(state.pairs[0].step, S[:, 1])


def test_memory_uses_first_model_counts_and_floor_halving():
    params = xr.Parameters(m0=2, m_max=20, q=3)
    assert update_capacity(params, 20, 9, 2, 9, 5, 1) == (4, 0)
    assert update_capacity(params, 20, 9, 2, 9, 0, 1) == (11, 0)
    assert update_capacity(params, 20, 9, 2, 9, 0, 2) == (9, 0)
    assert update_capacity(params, 20, 9, 2, 8, 0, 1) == (9, 0)
    assert update_capacity(params, 20, 9, 0, 9, 4, 1) == (9, 0)


@pytest.mark.parametrize("seed", range(5))
def test_modelstep_matches_independent_physical_gram_formulas(seed):
    rng = np.random.default_rng(seed)
    n, p = 9, 3
    B = rng.normal(size=(n, n))
    A = B.T @ B + np.eye(n)
    S = rng.normal(size=(n, p))
    Y = A @ S
    g = rng.normal(size=n)
    state = state_from_pairs(S, Y, g)
    params = xr.Parameters(m0=p, m_max=p, safeguard=False, trial="midpoint", floor=True)
    result = xr.model_step(state, params)
    C, G = S.T @ Y, S.T @ S
    T = xr.latest(C)
    w = -np.linalg.solve(T, S.T @ g)
    gv = g + Y @ w
    d = -gv + S @ np.linalg.solve(C.T, Y.T @ gv)
    eigen = eigvalsh(T, G)
    lo, hi = eigen[0] / 2, eigen[-1] * 2
    b, dd = S.T @ d, d @ d
    low = lo + lo**2 * b @ np.linalg.solve(T - lo * G, b) / dd
    high = hi - hi**2 * b @ np.linalg.solve(hi * G - T, b) / dd
    rho = (low + high) / 2
    if low > high:
        rho = np.clip(rho, lo, hi)
    rho = min(max(rho, high / (2 * (1 - params.sigma) - params.eta0)), high)
    expected = S @ w - (g @ d / (rho * dd)) * d
    np.testing.assert_allclose(result.u, expected, rtol=3e-13, atol=3e-13)
    np.testing.assert_allclose(result.virtual_g, gv, rtol=3e-13, atol=3e-13)
    np.testing.assert_allclose(Y.T @ result.direction, 0, atol=1e-11)
    np.testing.assert_allclose(state.bounds, [lo, hi], rtol=3e-13)


def test_full_dimension_branch_has_no_missing_curvature_trial():
    S, A = np.eye(3), np.diag([1.0, 2.0, 5.0])
    state = state_from_pairs(S, A)
    result = xr.model_step(state, xr.Parameters(m0=3, m_max=3, safeguard=False))
    np.testing.assert_allclose(result.u, -np.linalg.solve(A, state.g))
    assert result.rho is None
    np.testing.assert_array_equal(result.direction, np.zeros(3))


def test_f_term_is_omitted_instead_of_clipped():
    pair = xr.Pair.observe(np.array([1.0, 0.0]), np.array([2.0, 0.0]), delta=1.0)
    pair.pairing = 2.0
    corrected, terms, omitted = value_model([pair], np.array([[2.0]]), xr.Parameters(values=True))
    assert omitted == 1 and terms[0] == 0 and corrected[0, 0] == 2


def test_f_gate_preserves_observed_skew_not_just_real_positivity():
    S = np.eye(3)[:, :2]
    C = np.array([[1.0, 0.3], [0.9, 1.0]])
    state = state_from_pairs(S, S @ C)
    for pair in state.pairs:
        pair.delta = 1 / 12
        pair.pairing = 1.0
    expected = state.x - S @ np.linalg.solve(xr.latest(C), S.T @ state.g)
    corrected = xr.latest(C) - 0.5 * np.eye(2)
    assert np.linalg.eigvalsh(corrected)[0] > 0
    assert np.linalg.eigvalsh(corrected + 1j * (C - C.T))[0] < 0
    result = xr.model_step(state, xr.Parameters(m0=2, m_max=2, values=True))
    np.testing.assert_allclose(result.virtual_x, expected)
    assert state.counters["nF_fallback"] == 1


def test_anchor_pairing_transport_includes_probe_then_accepted_displacement():
    pair = xr.Pair.observe(np.array([2.0, 0.0]), np.array([4.0, 2.0]), delta=0.1)
    pair.transport(np.array([0.3, -0.2]))
    assert pair.pairing == pytest.approx(np.array([4.0, 2.0]) @ np.array([0.3, -0.2]) / 4)
    assert pair.euclidean == pytest.approx(0.15)


@pytest.mark.parametrize("values", [False, True])
def test_small_full_window_virtual_points_match_independent_cg(values):
    problem = Quad(n=6, kappa=10.0)
    reference = cg_iterates(problem, problem.x0, problem.n)
    seen = []
    result = run_gtol(
        xr.solve,
        problem,
        dict(
            values=values,
            m0=6,
            m_max=6,
            safeguard=False,
            hook=lambda x, g, p: seen.append((p, x.copy())),
        ),
    )
    assert result["status"] == "converged"
    for p, x in seen:
        np.testing.assert_allclose(x, reference[p], rtol=2e-7, atol=2e-8)
    assert result["info"]["counters"]["nrank_deleted"] == 0


def test_f_is_exactly_inactive_on_numerically_resolved_quadratic_values():
    problem = Quad(n=12, kappa=30.0)
    traces = [[], []]
    runs = [
        run_gtol(xr.solve, problem, dict(values=bool(i), m0=4, m_max=12, trace=traces[i]))
        for i in range(2)
    ]
    assert all(row["status"] == "converged" for row in runs)
    assert traces[0] == traces[1]
    assert runs[1]["info"]["counters"]["nF_applied"] == 0


def test_extremely_scaled_pairs_do_not_change_model_step():
    rng = np.random.default_rng(7)
    S = rng.normal(size=(8, 3))
    A = np.diag(np.arange(1.0, 9.0))
    params = xr.Parameters(m0=3, m_max=3, safeguard=False)
    first = xr.model_step(state_from_pairs(S, A @ S), params)
    scales = np.array([1e-100, 1e-20, 1e100])
    second = xr.model_step(state_from_pairs(S * scales, (A @ S) * scales), params)
    np.testing.assert_allclose(first.u, second.u, rtol=3e-13, atol=3e-13)


@pytest.mark.parametrize("seed", range(5))
def test_schur_interval_contains_true_spd_curvature(seed):
    rng = np.random.default_rng(seed)
    A = np.diag(np.geomspace(1.0, 100.0, 12))
    Q, _ = np.linalg.qr(rng.normal(size=(12, 4)))
    Y = A @ Q
    d = rng.normal(size=12)
    d -= Y @ np.linalg.solve(Y.T @ Y, Y.T @ d)
    low, high = consistency_interval(Q.T @ A @ Q, Q, d, (0.5, 200.0))
    assert low <= d @ A @ d / (d @ d) <= high


@pytest.mark.parametrize("values", [False, True])
def test_direct_armijo_resolves_large_constant_offset_without_relaxing_target(values):
    """A function offset must not force chi=2 rejections of resolved gradients."""

    class OffsetQuadratic:
        name = "OFFSET-QUADRATIC"
        n = 3
        x0 = np.array([0.2, 0.15, 0.1])
        meta = {}
        err_from_f = False
        fstar = None
        matrix = np.diag([1.0, 2.0, 5.0])

        def f(self, x):
            return 1e16 + 0.5 * x @ self.matrix @ x

        def grad(self, x):
            return self.matrix @ x

        def fg(self, x):
            return self.f(x), self.grad(x)

    problem = OffsetQuadratic()
    # Both rounded endpoint values may coincide. The mathematically
    # equivalent direct predicate avoids subtracting them and dividing by
    # a tiny slope; no epsilon is added and the actual target is unchanged.
    slope = -1e-12
    assert xr._chi(1e16, 1e16, slope) == 2.0
    assert 1e16 <= 1e16 + 1e-4 * slope
    result = run_gtol(xr.solve, problem, dict(values=values, m0=3, m_max=3), rel=1e-10, budget=100)
    assert result["status"] == "converged", result
    point = np.asarray(result["hit"]["x"])
    assert np.linalg.norm(problem.grad(point)) <= 1e-10 * np.linalg.norm(problem.grad(problem.x0))
    assert result["n_pts"] <= 6


def test_observed_pair_slope_and_transport_use_actual_representable_displacement(monkeypatch):
    """A small intended step at a large anchor rounds to a different displacement."""
    from xrbench.methods._xr_model import ModelResult

    anchor = np.full(2, float(2**40))
    gradient = np.ones(2)
    intended = np.array([-0.0003, -0.00055])
    tested = anchor + intended
    actual = tested - anchor
    assert not np.array_equal(actual, intended)
    previous = xr.Pair.observe(np.array([1.0, 0.0]), np.array([2.0, 0.0]))
    state = xr.State(anchor.copy(), 0.0, gradient.copy(), 2, 1.0, 1e-10, 1e10)
    state.pairs = [previous]

    class EndpointOracle:
        def __init__(self):
            self.points = []

        def fg(self, point):
            self.points.append(point.copy())
            displacement = point - anchor
            return float(gradient @ displacement + 0.5 * displacement @ displacement), (
                gradient + displacement
            )

    oracle = EndpointOracle()
    model = ModelResult(intended, 1, 0, anchor.copy(), gradient.copy(), -gradient, 1.0)
    monkeypatch.setattr(xr, "model_step", lambda *args, **kwargs: model)
    trace = []
    assert xr.iterate(oracle, state, xr.Parameters(m0=2, m_max=2, values=True), trace=trace)
    assert len(oracle.points) == 1
    np.testing.assert_array_equal(oracle.points[0], tested)
    np.testing.assert_array_equal(state.x, tested)
    observed = state.pairs[-1]
    np.testing.assert_array_equal(observed.step, actual)
    np.testing.assert_array_equal(observed.image, actual)
    assert trace[0]["slope"] == float(gradient @ actual)
    assert previous.pairing == 2 * actual[0]
    assert previous.euclidean == actual[0]
    assert observed.pairing == pytest.approx(float(observed.s @ observed.y), rel=2e-15)


@pytest.mark.parametrize("epsilon", [1e-3, 1e-5])
def test_bounded_changing_secants_can_have_large_certified_ritz_range(epsilon):
    """The Hermitian certificate does not bound physical Ritz curvature by ||A_i||."""
    S = np.array([[1.0, 1.0], [0.0, epsilon]])
    Y = S.copy()
    Y[:, 0] *= 1.5  # A0=1.5I, A1=I, both uniformly bounded and positive.
    C = S.T @ Y
    H = xr.latest(C) + 1j * (C - C.T)
    assert np.linalg.eigvalsh(H)[0] > 0
    assert unrefuted_suffix(C) == 0
    state = state_from_pairs(S, Y)
    params = xr.Parameters(m0=2, m_max=2, trial="midpoint", floor=True)
    result = xr.model_step(state, params)
    assert result.deleted == 0 and state.counters["nrank_deleted"] == 0
    # Analytic determinant: (1-lambda) * [1/2 + (3/2-lambda)*epsilon^2].
    np.testing.assert_allclose(state.bounds, [0.5, 3.0 + epsilon**-2], rtol=3e-13)
    previous = state.bounds
    state.pairs = [xr.Pair.observe(np.array([1.0, 0.0]), np.array([1.0, 0.0]))]
    xr.model_step(state, params)
    # The literal running-bound rule does not forget an earlier large Ritz
    # value just because a later window has unit physical curvature.
    assert state.bounds == previous


@pytest.mark.parametrize("values", [False, True])
def test_practical_secant_trial_matches_independent_physical_formula_without_spectra(
    monkeypatch, values
):
    from xrbench.methods import _xr_model

    rng = np.random.default_rng(91)
    S = rng.normal(size=(8, 3))
    A = np.diag(np.arange(1.0, 9.0))
    Y = A @ S
    gradient = rng.normal(size=8)
    state = state_from_pairs(S, Y, gradient)
    # An old interval must neither determine the new trial nor be updated.
    state.bounds = (1e-30, 1e100)
    old_bounds = state.bounds

    def forbidden(*args, **kwargs):
        raise AssertionError("the default practical path called spectral diagnostics")

    monkeypatch.setattr(_xr_model, "eigvalsh", forbidden)
    monkeypatch.setattr(_xr_model, "_orthogonal_model", forbidden)
    monkeypatch.setattr(_xr_model, "consistency_interval", forbidden)
    result = xr.model_step(state, xr.Parameters(m0=3, m_max=3, values=values, safeguard=False))
    C = S.T @ Y
    w = -np.linalg.solve(xr.latest(C), S.T @ gradient)
    virtual = gradient + Y @ w
    direction = -virtual + S @ np.linalg.solve(C.T, Y.T @ virtual)
    rho = float(S[:, -1] @ Y[:, -1] / (S[:, -1] @ S[:, -1]))
    expected = S @ w - (gradient @ direction / (rho * (direction @ direction))) * direction
    np.testing.assert_allclose(result.u, expected, rtol=3e-13, atol=3e-13)
    assert result.rho == pytest.approx(rho)
    assert state.bounds == old_bounds


def test_empty_window_and_safeguard_use_the_fresh_scale_not_historical_bounds(monkeypatch):
    state = xr.State(np.zeros(2), 0.0, np.ones(2), 2, 1.0, 0.01, 10.0)
    state.secant_curvature = 4.0
    state.bounds = (1e-30, 1e100)
    result = xr.model_step(state, xr.Parameters(m0=2, m_max=2))
    np.testing.assert_array_equal(result.u, np.array([-0.25, -0.25]))
    # The norm test deliberately rejects 1/4. The same fresh scale is
    # clipped to the allowed fallback interval [1/c2,1/c1]=[10,100].
    state.c2 = 0.1
    result = xr.model_step(state, xr.Parameters(m0=2, m_max=2))
    assert result.safeguarded
    np.testing.assert_array_equal(result.u, np.array([-0.1, -0.1]))
    assert state.secant_curvature == 4.0
    assert state.bounds == (1e-30, 1e100)


@pytest.mark.parametrize("length,safeguarded", [(1.0, False), (0.5, False), (1.0, True)])
def test_lagged_directional_learning_uses_actual_unshortened_launch_only(length, safeguarded):
    from xrbench.methods._xr_model import ModelResult

    A = np.diag([2.0, 5.0])
    virtual = np.array([0.2, 0.3])
    direction = np.array([1.0, -2.0])
    tau = 0.125
    state = xr.State(np.zeros(2), 0.0, np.ones(2), 2, 1.0, 1e-10, 1e10)
    state.lagged = 7.0
    total = virtual + tau * direction
    model = ModelResult(total, 1, 0, virtual, A @ virtual, direction, 4.0, safeguarded)
    point = state.x + length * total
    xr._learn_lagged_curvature(state, model, point, A @ point, length)
    if length == 1.0 and not safeguarded:
        expected = float(direction @ A @ direction / (direction @ direction))
        assert state.lagged == pytest.approx(expected, rel=2e-15)
    else:
        assert state.lagged == 7.0


class _CountedQuadratic:
    name = "COUNTED-QUADRATIC"
    n = 1
    x0 = np.ones(1)
    meta = {}
    err_from_f = False
    fstar = None

    def __init__(self, nonfinite_gradient_at_zero=False):
        self.f_points = []
        self.g_points = []
        self.nonfinite_gradient_at_zero = nonfinite_gradient_at_zero

    def f(self, x):
        self.f_points.append(float(x[0]))
        return float(5 * x[0] ** 2)

    def grad(self, x):
        self.g_points.append(float(x[0]))
        return np.array([np.nan if self.nonfinite_gradient_at_zero and x[0] == 0 else 10 * x[0]])

    def fg(self, x):
        return self.f(x), self.grad(x)


def _mock_model(state, displacement):
    from xrbench.methods._xr_model import ModelResult

    return ModelResult(
        np.array([displacement]), 0, 0, state.x.copy(), state.g.copy(), -state.g, 10.0
    )


def test_after_one_probe_rejected_trials_do_not_compute_gradients(monkeypatch):
    from xrbench.oracle import Oracle

    problem = _CountedQuadratic()
    oracle = Oracle(problem, budget=100, max_time=10)
    params = xr.Parameters(m0=1, m_max=1)
    state = xr.initialize(oracle, problem.x0, params)
    calls = iter([-3.0, -4.0])
    monkeypatch.setattr(xr, "model_step", lambda state, *args: _mock_model(state, next(calls)))
    trace = []
    assert xr.iterate(oracle, state, params, trace=trace)
    assert state.counters["nprobe"] == 1
    assert [row["gradient_evaluated"] for row in trace] == [True, False, True]
    assert problem.f_points == [1.0, -2.0, -3.0, 0.0]
    assert problem.g_points == [1.0, -2.0, 0.0]
    assert (oracle.n_f_evals, oracle.n_g_evals, oracle.n_fg_evals) == (4, 3, 2)


def test_no_probe_uses_function_only_rejections_from_first_trial(monkeypatch):
    from xrbench.oracle import Oracle

    problem = _CountedQuadratic()
    oracle = Oracle(problem, budget=100, max_time=10)
    params = xr.Parameters(m0=1, m_max=1, probe=False)
    state = xr.initialize(oracle, problem.x0, params)
    monkeypatch.setattr(xr, "model_step", lambda state, *args: _mock_model(state, -3.0))
    assert xr.iterate(oracle, state, params)
    assert problem.f_points == [1.0, -2.0, 0.0]
    assert problem.g_points == [1.0, 0.0]
    assert (oracle.n_f_evals, oracle.n_g_evals, oracle.n_fg_evals) == (3, 2, 1)


@pytest.mark.parametrize("probe", [False, True])
def test_nonfinite_gradient_cannot_accept_or_enter_a_pair(monkeypatch, probe):
    from xrbench.oracle import Oracle

    problem = _CountedQuadratic(nonfinite_gradient_at_zero=True)
    oracle = Oracle(problem, budget=100, max_time=10)
    params = xr.Parameters(m0=1, m_max=1, probe=probe)
    state = xr.initialize(oracle, problem.x0, params)
    monkeypatch.setattr(xr, "model_step", lambda state, *args: _mock_model(state, -1.0))
    assert xr.iterate(oracle, state, params)
    assert state.counters["nrej"] == 1 and state.counters["nprobe"] == 0
    np.testing.assert_array_equal(state.x, np.array([0.9]))
    assert np.all(np.isfinite(state.g))
    assert len(state.pairs) == 1 and all(np.all(np.isfinite(pair.image)) for pair in state.pairs)
