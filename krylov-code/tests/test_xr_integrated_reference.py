"""Independent physical-coordinate reference for the manuscript ModelStep.

The implementation uses normalized pairs and a newest-first QR factorization.
The reference below instead builds the original physical Gram matrices. It
reconstructs both the practical fresh-secant trial and the Ritz/Schur diagnostic
directly, catching transpose, permutation and pair-scaling mistakes.
"""

import numpy as np
import pytest
from scipy.linalg import eigvalsh

from xrbench.methods._xr_model import Pair, Parameters, State, model_step


def physical_model_step(state, params):
    """Literal formulas, without importing any production matrix helper."""
    S = np.column_stack([pair.step for pair in state.pairs])
    Y = np.column_stack([pair.image for pair in state.pairs])
    C = S.T @ Y
    p = C.shape[0]
    T = np.array([[C[min(i, j), max(i, j)] for j in range(p)] for i in range(p)])
    selected = T.copy()
    if params.values:
        terms = []
        for i, pair in enumerate(state.pairs):
            phi = pair.pairing * pair.scale**2
            defect = pair.delta * pair.scale**2
            split = phi / C[i, i] - 0.5 if params.split == "model" else pair.euclidean - 0.5
            term = 12 * split * defect
            terms.append(0 if abs(term) > C[i, i] / 2 else term)
        corrected = T - np.diag(terms)
        gate = corrected + 1j * (C - C.T) / params.theta
        if np.linalg.eigvalsh(gate).min() > 0:
            selected = corrected
    w = -np.linalg.solve(selected, S.T @ state.g)
    correction = S @ w
    if p == len(state.x):
        return correction
    virtual = state.g + Y @ w
    d = -virtual + S @ np.linalg.solve(C.T, Y.T @ virtual)
    if np.linalg.norm(d) == 0:
        return correction
    unit = d / np.linalg.norm(d)
    if params.trial == "secant":
        # Read the newest incoming actual pair, independently of any model
        # coordinate normalization or historical spectral enclosure.
        newest = state.pairs[-1]
        rho = newest.step @ newest.image / (newest.step @ newest.step)
        return correction - (state.g @ unit / rho) * unit
    G = S.T @ S
    ritz = eigvalsh(T, G)
    lower, upper = ritz[0] / params.inflation, ritz[-1] * params.inflation
    if state.bounds is not None:
        lower, upper = min(lower, state.bounds[0]), max(upper, state.bounds[1])
    b = S.T @ unit
    lo = lower + lower**2 * (b @ np.linalg.solve(T - lower * G, b))
    hi = upper - upper**2 * (b @ np.linalg.solve(upper * G - T, b))
    rho = (lo + hi) / 2
    if lo > hi:
        rho = np.clip(rho, lower, upper)
    if params.floor and hi > 0:
        rho = min(max(rho, hi / (2 * (1 - params.sigma) - params.eta0)), hi)
    return correction - (state.g @ unit / rho) * unit


@pytest.mark.parametrize("values", [False, True])
@pytest.mark.parametrize("p", [1, 2, 3, 6])
@pytest.mark.parametrize("trial", ["secant", "midpoint"])
def test_model_step_matches_independent_physical_reference(values, p, trial):
    rng = np.random.default_rng(482 + p)
    n = 6
    for repetition in range(8):
        B = rng.normal(size=(n, n))
        A = B.T @ B + np.eye(n)
        S = rng.normal(size=(n, p))
        Y = A @ S + 0.002 * rng.normal(size=(n, p))
        # Congruence scaling and sign changes exercise the production QR
        # coordinates against a reference using the physical step matrices.
        scales = np.geomspace(0.25, 4.0, p) * rng.choice([-1, 1], p)
        S, Y = S * scales, Y * scales
        x, g = rng.normal(size=n), rng.normal(size=n)
        pairs = [Pair.observe(S[:, i], Y[:, i], 0.001 * rng.normal()) for i in range(p)]
        for pair in pairs:
            pair.transport(x)
        params = Parameters(
            m0=n,
            m_max=n,
            values=values,
            safeguard=False,
            trial=trial,
            floor=trial == "midpoint",
            split="model" if repetition % 2 else "euclidean",
        )
        bounds = None if repetition % 2 else (0.01, 1e3)
        state = State(x, 1.0, g, n, 1.0, 1e-10, 1e10, pairs=pairs, bounds=bounds)
        expected = physical_model_step(state, params)
        result = model_step(state, params)
        assert result.first_pairs == p
        assert result.deleted == 0
        assert len(state.pairs) == p
        np.testing.assert_allclose(result.u, expected, rtol=2e-9, atol=2e-10)
