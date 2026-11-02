"""Independent objective/gradient and streamed data preparation checks."""

import importlib.util
import json
from pathlib import Path

import numpy as np
import pytest
from scipy.special import expit

from xrbench.problems import libsvm


@pytest.mark.parametrize("storage", ["dense", "csr"])
def test_streamed_data_and_logistic_gradient(tmp_path, monkeypatch, storage):
    module_path = Path(__file__).parents[1] / "scripts/prepare_libsvm.py"
    spec = importlib.util.spec_from_file_location("prepare_libsvm_test", module_path)
    prepare = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(prepare)
    raw = tmp_path / "raw.txt"
    raw.write_text("2 1:3 3:4\n1 2:-2\n2\n1 1:-1 2:2 3:2\n")
    dataset = dict(name="test", rows=4, features=3, storage=storage, file="test")
    prepare.prepare(dataset, tmp_path, raw)
    receipt = json.loads((tmp_path / "test/receipt.json").read_text())
    prepare.verify(tmp_path / "test", receipt)
    monkeypatch.setenv("XR_LIBSVM_DATA", str(tmp_path))
    monkeypatch.setattr(libsvm, "catalog", lambda: dict(datasets=[dataset]))
    libsvm.validate_prepared_data({"test": receipt})
    problem = libsvm.LogisticProblem("test", 0.013)
    design = np.array([[.6, 0., .8, 1.], [0., -1., 0., 1.],
                       [0., 0., 0., 1.], [-1/3, 2/3, 2/3, 1.]])
    labels = np.array([1., -1., 1., -1.])
    x = np.array([.4, -.9, 1.3, -.2])
    margin = labels * (design @ x)
    expected_f = np.mean(np.logaddexp(0., -margin)) + .013/2 * (x @ x)
    expected_g = design.T @ (-labels * expit(-margin)) / 4 + .013*x
    assert problem.f(x) == pytest.approx(expected_f, rel=2e-15)
    np.testing.assert_allclose(problem.grad(x), expected_g, rtol=3e-15, atol=2e-16)
    f, g = problem.fg(x)
    assert f == problem.f(x)
    np.testing.assert_array_equal(g, problem.grad(x))
    for j in range(4):
        delta = np.eye(4)[j] * 1e-5
        assert g[j] == pytest.approx((problem.f(x+delta)-problem.f(x-delta))/2e-5, abs=2e-10)
    weights = expit(margin) * expit(-margin)
    hessian = design.T @ (weights[:, None]*design)/4 + .013*np.eye(4)
    assert np.linalg.eigvalsh(hessian).min() >= .013 - 1e-15
    # The intercept contributes to the gradient and has its own ridge penalty.
    assert problem.n == 4
    assert np.all(problem.x0 == 0)
    assert np.isfinite(problem.f(np.full(4, 1e4)))
    assert np.all(np.isfinite(problem.grad(np.full(4, -1e4))))
    # A changed prepared array with an unchanged receipt is refused before run.
    label_path = tmp_path / "test/labels.npy"
    changed = np.load(label_path).copy()
    changed[0] *= -1
    np.save(label_path, changed)
    with pytest.raises(ValueError, match="data array changed"):
        libsvm.validate_prepared_data({"test": receipt})


def test_prepared_data_checksum_tampering_detected(tmp_path):
    spec = importlib.util.spec_from_file_location(
        "prepare_libsvm_test", Path(__file__).parents[1] / "scripts/prepare_libsvm.py")
    prepare = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(prepare)
    path = tmp_path / "array.npy"
    np.save(path, np.array([1., 2.]))
    receipt = dict(arrays={"array.npy": prepare.sha(path)})
    np.save(path, np.array([1., 3.]))
    with pytest.raises(ValueError, match="checksum mismatch"):
        prepare.verify(tmp_path, receipt)


class _CountedDesign:
    """Count forward/transpose products without changing either numerical map."""
    def __init__(self, matrix, counts=None, transposed=False):
        self.matrix = matrix
        self.counts = counts if counts is not None else {"forward": 0, "transpose": 0}
        self.transposed = transposed

    def __matmul__(self, x):
        self.counts["transpose" if self.transposed else "forward"] += 1
        return self.matrix @ x

    @property
    def T(self):
        return _CountedDesign(self.matrix.T, self.counts, not self.transposed)


def _cache_problem(storage):
    from scipy import sparse

    matrix = np.array([[.6, 0., .8], [0., -1., 0.], [0., 0., 0.], [-1/3, 2/3, 2/3]])
    problem = libsvm.LogisticProblem.__new__(libsvm.LogisticProblem)
    problem.A = _CountedDesign(sparse.csr_matrix(matrix) if storage == "csr" else matrix)
    problem.y = np.array([1., -1., 1., -1.])
    problem.samples, problem.n, problem.regularization = 4, 4, .013
    problem._margin_key = problem._cached_margin = None
    return problem


@pytest.mark.parametrize("storage", ["dense", "csr"])
@pytest.mark.parametrize("first", ["f", "fg"])
def test_exact_margin_cache_shares_forward_work_without_hidden_gradient(storage, first):
    problem = _cache_problem(storage)
    x = np.array([.4, -.9, 1.3, -.2])
    if first == "f":
        value = problem.f(x)
        assert problem.A.counts == {"forward": 1, "transpose": 0}
        gradient = problem.grad(x)
    else:
        value, gradient = problem.fg(x)
    assert problem.A.counts == {"forward": 1, "transpose": 1}
    assert problem.f(x.copy()) == value
    np.testing.assert_array_equal(problem.grad(x.copy()), gradient)
    assert problem.A.counts == {"forward": 1, "transpose": 2}
    assert isinstance(problem._margin_key, bytes)
    assert not problem._cached_margin.flags.writeable
    with pytest.raises(ValueError, match="read-only"):
        problem._cached_margin[0] = 0
    # Public gradient outputs never alias the retained margin or each other.
    expected = gradient.copy()
    gradient[:] = 1e100
    np.testing.assert_array_equal(problem.grad(x), expected)
    assert problem.A.counts == {"forward": 1, "transpose": 3}


@pytest.mark.parametrize("storage", ["dense", "csr"])
def test_margin_cache_key_detects_caller_mutation_including_intercept(storage):
    problem = _cache_problem(storage)
    x = np.array([.4, -.9, 1.3, -.2])
    problem.f(x)
    old_key = problem._margin_key
    old_margin = problem._cached_margin.copy()
    x[-1] += .25
    f, g = problem.fg(x)
    accepted_point = x.copy()
    assert problem.A.counts == {"forward": 2, "transpose": 1}
    assert problem._margin_key != old_key
    np.testing.assert_allclose(problem._cached_margin - old_margin, .25 * problem.y, atol=2e-16)
    # Reuse of the same mutable input object must invalidate feature changes.
    x[0] += .5
    problem.grad(x)
    assert problem.A.counts == {"forward": 3, "transpose": 2}
    other = x + np.array([0., 0., -.2, 0.])
    problem.f(other)
    assert problem.A.counts == {"forward": 4, "transpose": 2}
    # This is deliberately a one-point cache; returning to x recomputes A@x.
    problem.f(x)
    assert problem.A.counts == {"forward": 5, "transpose": 2}
    # Numerical results remain those of a fresh adapter, independent of cache.
    fresh = _cache_problem(storage)
    np.testing.assert_array_equal(fresh.fg(accepted_point)[1], g)
    assert f == fresh.f(accepted_point)


def test_margin_cache_uses_exact_full_point_bytes():
    problem = _cache_problem("dense")
    x = np.zeros(4)
    problem.f(x)
    positive_key = problem._margin_key
    x[-1] = -0.
    problem.f(x)
    assert problem._margin_key != positive_key
    assert problem.A.counts == {"forward": 2, "transpose": 0}
