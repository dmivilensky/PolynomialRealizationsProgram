"""Arithmetic and reuse contracts of the optimized XR matrix assembly."""

import numpy as np
import pytest

from xrbench.methods import _xr_model
from xrbench.methods._gram import WindowGram


@pytest.mark.parametrize("dtype", [np.float64, np.complex128, np.int64])
def test_latest_preserves_original_entries_and_signed_zero_bytes(dtype):
    C = np.array([[2, -0.0, 3], [7, 4, -0.0], [-0.0, 8, 5]], dtype=dtype)
    expected = np.triu(C) + np.triu(C, 1).T
    np.testing.assert_array_equal(_xr_model.latest(C), expected)
    assert _xr_model.latest(C).tobytes() == expected.tobytes()


def test_chronological_gram_cache_and_arbitrary_fallback_match_original_arithmetic():
    rng = np.random.default_rng(237)
    S, Y = rng.normal(size=(2, 17, 9))
    steps, images = list(S.T), list(Y.T)
    optimized, original = WindowGram(), WindowGram()
    # Actual chronological suffix/append operations, followed by arbitrary
    # subsets and reorderings supported by the shared cache's original API.
    for indices in (
        [0, 1, 2],
        [1, 2, 0],
        [1, 2, 3],
        [1, 2, 3, 4],
        [3, 4],
        [5, 4, 3],
        [4, 6, 3],
        [],
    ):
        s = [steps[i] for i in indices]
        y = [images[i] for i in indices]
        expected = original._general_get(s, y)
        actual = optimized.get(s, y)
        assert actual.tobytes() == expected.tobytes()
        if indices:
            np.testing.assert_allclose(actual, S[:, indices].T @ Y[:, indices], atol=2e-15)


def test_reintroduced_old_pair_uses_the_general_cache_path(monkeypatch):
    rng = np.random.default_rng(81)
    S, Y = rng.normal(size=(2, 17, 3))
    steps, images = list(S.T), list(Y.T)
    cache = WindowGram()
    previous = cache.get(steps, images).copy()
    calls = []
    original = cache._general_get

    def watched(*args, **kwargs):
        calls.append(1)
        return original(*args, **kwargs)

    monkeypatch.setattr(cache, "_general_get", watched)
    order = [1, 2, 0]
    result = cache.get([steps[i] for i in order], [images[i] for i in order])
    assert calls == [1]
    assert result.tobytes() == previous[np.ix_(order, order)].tobytes()


def test_provided_pair_matrices_avoid_repeated_stacking(monkeypatch):
    rng = np.random.default_rng(728)
    S, Y = rng.normal(size=(2, 13, 5))
    steps, images = list(S.T), list(Y.T)
    matrices = [(S[:, :3].copy(), Y[:, :3].copy()), (S[:, 1:4].copy(), Y[:, 1:4].copy())]
    cache = WindowGram()

    def forbidden(*args, **kwargs):
        raise AssertionError("the already stacked pair matrices were rebuilt")

    monkeypatch.setattr(np, "column_stack", forbidden)
    for indices, (sm, ym) in zip((range(3), range(1, 4)), matrices):
        actual = cache.get([steps[i] for i in indices], [images[i] for i in indices], Sm=sm, Ym=ym)
        np.testing.assert_allclose(actual, sm.T @ ym, atol=2e-15)


def test_value_correction_reuses_the_supplied_latest_model(monkeypatch):
    pair = _xr_model.Pair.observe(np.array([1.0, 0.0]), np.array([2.0, 0.0]), delta=0.1)
    pair.pairing = 2.0

    def forbidden(*args, **kwargs):
        raise AssertionError("the existing latest model was rebuilt")

    monkeypatch.setattr(_xr_model, "latest", forbidden)
    corrected, terms, omitted = _xr_model.value_model(
        [pair], np.array([[2.0]]), _xr_model.Parameters(values=True), base=np.array([[2.0]])
    )
    assert omitted == 0
    np.testing.assert_allclose(terms, [0.6])
    np.testing.assert_allclose(corrected, [[1.4]])
