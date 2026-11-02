"""Theoretical XRFC: virtual/evaluated separation and actual CG identities."""

import numpy as np
import pytest
from _infra import Quad, cg_iterates

from xrbench.methods import xrfc


@pytest.mark.parametrize("trial", [0.1, 0.2, 0.3])
def test_arbitrary_nonzero_trials_have_exact_virtual_cg_profile(trial):
    problem = Quad(n=6, kappa=10.0)
    rows = xrfc.operator_cycle(
        [problem.A] * 6, problem.grad(problem.x0), trial=trial, output_operator=problem.A
    )
    reference = cg_iterates(problem, problem.x0, 6)
    for k, row in enumerate(rows):
        np.testing.assert_allclose(
            problem.x0 + row["output"], reference[k + 1], rtol=3e-7, atol=3e-8
        )
        assert not row["output_evaluated"]
    np.testing.assert_allclose(rows[-1]["semantic_output_gradient"], 0.0, atol=1e-7)


def test_virtual_output_does_not_require_a_gradient_query():
    class Oracle:
        def __init__(self, A):
            self.A, self.calls = A, 0

        def fg(self, x):
            self.calls += 1
            return 0.5 * x @ self.A @ x, self.A @ x

    A = np.diag([1.0, 2.0])
    oracle, state = Oracle(A), {}
    x = np.array([1.0, 1.0])
    gradient = A @ x
    _, _, output, _ = xrfc.advance(oracle, x, gradient, state, 0, trial=0.2)
    assert oracle.calls == 1
    assert not np.array_equal(output, x + 0.2 * (-gradient))


def test_zero_trial_is_rejected_instead_of_silent_restart():
    with pytest.raises(ValueError):
        xrfc.operator_cycle([np.eye(2)], np.ones(2), trial=0.0)
