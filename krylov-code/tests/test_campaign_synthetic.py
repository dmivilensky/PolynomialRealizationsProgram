"""Diagnostics reuse actual objective work without exposing extra information."""

import numpy as np
import pytest

from xrbench.problems.synthetic import SmoothQuadratic, exp_remainder


class CountedMatrix:
    def __init__(self, matrix):
        self.matrix = matrix
        self.calls = 0

    def __matmul__(self, x):
        self.calls += 1
        return self.matrix @ x


@pytest.mark.parametrize("epsilon", [0.0, 0.1])
@pytest.mark.parametrize("evaluation", ["f", "grad", "fg"])
def test_energy_diagnostic_adds_no_matrix_action_after_real_evaluation(epsilon, evaluation):
    problem = SmoothQuadratic(7, 100.0, epsilon, 2)
    matrix = problem.A.copy()
    problem.A = CountedMatrix(matrix)
    x = problem.x0.copy()
    getattr(problem, evaluation)(x)
    assert problem.A.calls == 1  # setup did not pre-seed a free initial action
    expected = np.sqrt(x @ matrix @ x) / problem.initial_energy
    assert problem.err(x) == pytest.approx(expected)
    assert problem.err(x.copy()) == pytest.approx(expected)
    assert problem.A.calls == 1
    problem.f(x)
    problem.grad(x)
    assert problem.A.calls == 1


def test_cache_is_safe_under_solver_point_and_gradient_mutations():
    problem = SmoothQuadratic(5, 10.0)
    matrix = problem.A.copy()
    problem.A = CountedMatrix(matrix)
    x = problem.x0.copy()
    _, gradient = problem.fg(x)
    gradient[:] = 0.0
    assert np.allclose(problem.grad(x), matrix @ x)
    x[0] += 0.125
    assert problem.err(x) == pytest.approx(np.sqrt(x @ matrix @ x) / problem.initial_energy)
    assert problem.A.calls == 2
    assert np.allclose(problem.grad(x), matrix @ x)


def test_perturbed_objective_and_gradient_keep_the_exact_known_target():
    problem = SmoothQuadratic(8, 100.0, 0.3, 1)
    x = 0.5 * problem.x0
    expected_f = 0.5 * x @ problem.A @ x + 0.3 * exp_remainder(problem.Ac.T @ x).sum()
    expected_g = problem.A @ x + 0.3 * problem.Ac @ np.expm1(problem.Ac.T @ x)
    value, gradient = problem.fg(x)
    assert value == pytest.approx(expected_f, rel=1e-14)
    assert np.allclose(gradient, expected_g, rtol=1e-14, atol=1e-14)
    zero = np.zeros(problem.n)
    assert problem.f(zero) == 0.0
    assert np.array_equal(problem.grad(zero), zero)
    assert problem.err(zero) == 0.0
