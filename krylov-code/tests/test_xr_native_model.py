"""C ModelStep against independent physical-coordinate formulas and gates."""

from dataclasses import asdict

import numpy as np
import pytest
from test_xr import state_from_pairs
from test_xr_integrated_reference import physical_model_step

from xrbench.methods import xr
from xrbench.methods.xr_native import debug_model


def snapshot(state):
    return dict(
        x=state.x,
        f=state.f,
        g=state.g,
        capacity=state.capacity,
        tau0=state.tau0,
        c1=state.c1,
        c2=state.c2,
        bounds=state.bounds,
        secant_curvature=state.secant_curvature,
        lagged=state.lagged,
        pairs=[
            dict(
                step=pair.step,
                image=pair.image,
                delta=pair.delta,
                pairing=pair.pairing,
                euclidean=pair.euclidean,
            )
            for pair in state.pairs
        ],
    )


@pytest.mark.parametrize("values", [False, True])
@pytest.mark.parametrize("p", [1, 2, 3, 6])
@pytest.mark.parametrize("trial", ["secant", "midpoint"])
def test_native_matches_independent_physical_reference(values, p, trial):
    rng = np.random.default_rng(482 + p)
    n = 6
    for repetition in range(8):
        B = rng.normal(size=(n, n))
        A = B.T @ B + np.eye(n)
        S = rng.normal(size=(n, p))
        Y = A @ S + 0.002 * rng.normal(size=(n, p))
        scales = np.geomspace(0.25, 4.0, p) * rng.choice([-1, 1], p)
        S, Y = S * scales, Y * scales
        x, g = rng.normal(size=n), rng.normal(size=n)
        pairs = [xr.Pair.observe(S[:, i], Y[:, i], 0.001 * rng.normal()) for i in range(p)]
        for pair in pairs:
            pair.transport(x)
        params = xr.Parameters(
            m0=n,
            m_max=n,
            values=values,
            safeguard=False,
            trial=trial,
            floor=trial == "midpoint",
            split="model" if repetition % 2 else "euclidean",
        )
        bounds = None if repetition % 2 else (0.01, 1e3)
        state = xr.State(x, 1.0, g, n, 1.0, 1e-10, 1e10, pairs=pairs, bounds=bounds)
        expected = physical_model_step(state, params)
        result = debug_model(snapshot(state), params)
        assert result["first_pairs"] == p and result["deleted"] == 0
        assert result["pair_indices"] == list(range(p))
        np.testing.assert_allclose(result["u"], expected, rtol=2e-9, atol=2e-10)
        if p < n:
            np.testing.assert_allclose(Y.T @ result["direction"], 0, atol=5e-10)


def test_native_keeps_the_longest_independent_chronological_suffix():
    S = np.array([[1.0, 0.0, 1.0], [0.0, 1.0, 0.0], [0.0, 0.0, 0.0]])
    state = state_from_pairs(S, 2 * S)
    result = debug_model(snapshot(state), xr.Parameters(m0=3, m_max=3))
    assert result["pair_indices"] == [1, 2]
    assert result["first_pairs"] == 2 and result["deleted"] == 0
    assert result["counters"]["nrank_deleted"] == 1


@pytest.mark.parametrize("seed", range(8))
def test_native_hermitian_suffix_matches_independent_eigenvalue_test(seed):
    rng = np.random.default_rng(seed)
    C = rng.normal(size=(7, 7))
    np.fill_diagonal(C, rng.uniform(0.5, 3.0, 7))
    S = np.eye(9)[:, :7]
    for theta in (0.5, 1.0, 2.0):
        feasible = [
            j
            for j in range(7)
            if np.linalg.eigvalsh(xr.latest(C[j:, j:]) + 1j * (C[j:, j:] - C[j:, j:].T) / theta)[0]
            > 0
        ]
        state = state_from_pairs(S, S @ C)
        result = debug_model(
            snapshot(state), xr.Parameters(m0=7, m_max=7, theta=theta, safeguard=False)
        )
        assert result["deleted"] == min(feasible)
        assert result["pair_indices"] == list(range(min(feasible), 7))
        scales = rng.uniform(0.1, 10.0, 7) * rng.choice([-1, 1], 7)
        state = state_from_pairs(S * scales, (S @ C) * scales)
        scaled = debug_model(
            snapshot(state), xr.Parameters(m0=7, m_max=7, theta=theta, safeguard=False)
        )
        assert scaled["deleted"] == min(feasible)


def test_native_f_gate_keeps_original_skew_and_omits_oversized_terms():
    S = np.eye(3)[:, :2]
    C = np.array([[1.0, 0.3], [0.9, 1.0]])
    state = state_from_pairs(S, S @ C)
    for pair in state.pairs:
        pair.delta = 1 / 12
        pair.pairing = 1.0
    result = debug_model(snapshot(state), xr.Parameters(m0=2, m_max=2, values=True))
    expected = state.x - S @ np.linalg.solve(xr.latest(C), S.T @ state.g)
    np.testing.assert_allclose(result["virtual_x"], expected)
    assert result["counters"]["nF_fallback"] == 1
    state = state_from_pairs(np.array([[1.0], [0.0]]), np.array([[2.0], [0.0]]))
    state.pairs[0].pairing = 2.0
    state.pairs[0].delta = 1.0
    result = debug_model(snapshot(state), xr.Parameters(m0=1, m_max=1, values=True))
    assert result["counters"]["nF_omitted"] == 1
    assert result["counters"]["nF_applied"] == 0
    np.testing.assert_allclose(result["virtual_x"], [-0.5, 0.0])


def test_native_full_window_has_only_the_virtual_correction():
    state = state_from_pairs(np.eye(3), np.diag([1.0, 2.0, 5.0]))
    result = debug_model(snapshot(state), xr.Parameters(m0=3, m_max=3, safeguard=False))
    np.testing.assert_allclose(result["u"], -np.linalg.solve(np.diag([1.0, 2.0, 5.0]), state.g))
    assert result["rho"] is None
    np.testing.assert_array_equal(result["direction"], np.zeros(3))


def test_native_empty_window_and_safeguard_use_fresh_scale_not_old_bounds():
    state = xr.State(np.zeros(2), 0.0, np.ones(2), 2, 1.0, 0.01, 10.0)
    state.secant_curvature = 4.0
    state.bounds = (1e-30, 1e100)
    params = xr.Parameters(m0=2, m_max=2)
    result = debug_model(snapshot(state), params)
    np.testing.assert_array_equal(result["u"], [-0.25, -0.25])
    state.c2 = 0.1
    result = debug_model(snapshot(state), params)
    assert result["safeguarded"]
    np.testing.assert_array_equal(result["u"], [-0.1, -0.1])
    assert result["secant_curvature"] == 4.0
    assert result["bounds"] == [1e-30, 1e100] or result["bounds"] == (1e-30, 1e100)


def test_native_pair_normalization_is_invariant_under_extreme_signed_scaling():
    rng = np.random.default_rng(7)
    S = rng.normal(size=(8, 3))
    A = np.diag(np.arange(1.0, 9.0))
    params = xr.Parameters(m0=3, m_max=3, safeguard=False)
    first = debug_model(snapshot(state_from_pairs(S, A @ S)), asdict(params))
    scales = np.array([1e-100, -1e-20, 1e100])
    second = debug_model(snapshot(state_from_pairs(S * scales, (A @ S) * scales)), params)
    np.testing.assert_allclose(first["u"], second["u"], rtol=5e-13, atol=5e-13)


def test_native_zero_new_direction_keeps_the_partial_window_correction():
    state = state_from_pairs(
        np.array([[1.0], [0.0]]), np.array([[2.0], [0.0]]), gradient=np.array([3.0, 0.0])
    )
    result = debug_model(snapshot(state), xr.Parameters(m0=1, m_max=1, safeguard=False))
    np.testing.assert_array_equal(result["direction"], [0.0, 0.0])
    np.testing.assert_allclose(result["u"], [-1.5, 0.0])
    assert result["rho"] is None


@pytest.mark.parametrize("lagged,rho", [(1e9, 5.0), (1e-9, 2.0)])
def test_native_lagged_trial_clips_to_active_individual_secants(lagged, rho):
    S = np.eye(3)[:, :2]
    state = state_from_pairs(S, np.diag([2.0, 5.0, 10.0]) @ S)
    state.lagged, state.bounds = lagged, (1e-30, 1e100)
    result = debug_model(
        snapshot(state), xr.Parameters(m0=2, m_max=2, trial="lagged", safeguard=False)
    )
    assert result["rho"] == rho
    np.testing.assert_allclose(result["u"], [-0.5, -0.4, -3.0 / rho])


@pytest.mark.parametrize("seed", range(3))
@pytest.mark.parametrize("trial", ["secant", "midpoint"])
def test_native_cached_qr_and_gram_roll_ten_pairs_into_next_ten(seed, trial):
    """old_p=10, shared=9: append11/drop1 must retain immutable actual secants."""
    rng = np.random.default_rng(1000 + seed)
    n = 17
    S = rng.normal(size=(n, 11))
    A = np.diag(np.geomspace(1.0, 40.0, n))
    Y = A @ S
    params = xr.Parameters(m0=10, m_max=10, trial=trial, floor=trial == "midpoint", safeguard=False)
    first = state_from_pairs(S[:, :10], Y[:, :10], rng.normal(size=n), capacity=10)
    initial = debug_model(snapshot(first), params)
    np.testing.assert_allclose(
        initial["u"], physical_model_step(first, params), rtol=3e-10, atol=3e-11
    )
    incoming = state_from_pairs(S, Y, rng.normal(size=n), capacity=10)
    incoming.bounds = initial["bounds"]
    data = snapshot(incoming)
    data["qr_cache"] = initial["qr_cache"]
    data["gram_cache"] = initial["gram_cache"]
    expected_state = state_from_pairs(S[:, 1:], Y[:, 1:], incoming.g, capacity=10)
    expected_state.bounds = incoming.bounds
    expected = physical_model_step(expected_state, params)
    result = debug_model(data, params)
    assert result["pair_indices"] == list(range(1, 11))
    assert result["first_pairs"] == 10 and result["deleted"] == 0
    assert result["counters"]["nrank_deleted"] == 0
    np.testing.assert_allclose(result["u"], expected, rtol=3e-10, atol=3e-11)
    Q, R = result["qr_cache"]["Q"], result["qr_cache"]["R"]
    normalized = np.column_stack([pair.s for pair in expected_state.pairs])
    np.testing.assert_allclose(Q @ R, normalized[:, ::-1], atol=2e-13)


def test_native_qr_insertion_preserves_the_new_actual_pair():
    """Compiled QR insertion must not overwrite its immutable input column."""
    rng = np.random.default_rng(792)
    S = rng.normal(size=(8, 2))
    Y = np.diag(np.arange(1.0, 9.0)) @ S
    gradient = rng.normal(size=8)
    params = xr.Parameters(m0=3, m_max=3, safeguard=False)
    first = debug_model(snapshot(state_from_pairs(S[:, :1], Y[:, :1], capacity=3)), params)
    incoming = state_from_pairs(S, Y, gradient, capacity=3)
    data = snapshot(incoming)
    data["qr_cache"], data["gram_cache"] = first["qr_cache"], first["gram_cache"]
    result = debug_model(data, params)
    assert result["pair_indices"] == [0, 1]
    assert result["deleted"] == 0
    np.testing.assert_allclose(
        result["u"], physical_model_step(incoming, params), rtol=3e-12, atol=3e-12
    )
    Q, R = result["qr_cache"]["Q"], result["qr_cache"]["R"]
    normalized = np.column_stack([pair.s for pair in incoming.pairs])
    np.testing.assert_allclose(Q @ R, normalized[:, ::-1], atol=2e-13)
