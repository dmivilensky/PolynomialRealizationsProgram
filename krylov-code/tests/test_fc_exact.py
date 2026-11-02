"""Literal FC/RFC controls; no retired repeated-correction algorithms."""

import numpy as np
import pytest
from _infra import Quad, cg_iterates, run_gtol

from xrbench.methods import fc_exact


@pytest.mark.parametrize("correction", [False, True])
@pytest.mark.parametrize("search", ["quadratic", "root"])
def test_current_fc_rfc_reach_actual_quadratic_gradient_target(correction, search):
    result = run_gtol(
        fc_exact.solve,
        Quad(n=12, kappa=100.0),
        dict(correction=correction, search=search),
        budget=1000,
    )
    assert result["status"] == "converged", result
    assert result["info"]["search"]["kind"] == search


@pytest.mark.parametrize("correction", [False, True])
def test_operator_cycle_matches_independent_reference_cg(correction):
    problem = Quad(n=6, kappa=20.0)
    records = fc_exact.operator_cycle(
        [problem.A] * 6, [problem.A] * 6, problem.grad(problem.x0), correction=correction
    )
    reference = cg_iterates(problem, problem.x0, 6)
    for k, row in enumerate(records):
        np.testing.assert_allclose(
            problem.x0 + row["point"], reference[k + 1], atol=2e-11, rtol=2e-11
        )
        if correction:
            np.testing.assert_allclose(row["correction"], 0.0, atol=2e-11)
    assert records[-1]["final_virtual"] == correction
    assert not records[-1]["correction_evaluated"]


def test_correction_has_no_objective_decrease_filter():
    S = [np.array([1.0, 0.0, 0.0])]
    Y = [np.array([2.0, 0.4, 0.0])]
    g = np.array([1.0, 2.0, 3.0])
    d = fc_exact.direction(g, S, Y)
    z = np.diag([2.0, 3.0, 4.0]) @ d
    alpha = -g @ d / (d @ z)
    post = g + alpha * z
    move, applied = fc_exact.correction_displacement(S, Y, d, z, post)
    U = np.column_stack([S[0], d])
    H = np.block(
        [
            [np.array([[2.0]]), (S[0] @ z).reshape(1, 1)],
            [(z @ S[0]).reshape(1, 1), (d @ z).reshape(1, 1)],
        ]
    )
    assert applied
    np.testing.assert_allclose(move, -U @ np.linalg.solve(H, U.T @ post))


def test_rfc_gate_uses_retained_window_as_in_verified_rfcCorrection():
    S = [np.array([1.0, 0.0, 0.0])]
    Y = [np.array([1.0, 10.0, 0.0])]
    d = np.array([0.0, 1.0, 1.0])
    z = np.array([0.0, 1.0, 1.0])
    # The old 1x1 skew defect is zero; the augmented defect is large.
    U, Z = np.column_stack([S[0], d]), np.column_stack([Y[0], z])
    assert fc_exact.canonical_defect(U.T @ Z) > 1
    _, applied = fc_exact.correction_displacement(S, Y, d, z, np.ones(3))
    assert applied


def test_fc_direction_satisfies_observed_conjugacy_without_mutual_conjugacy():
    S = [np.array([1.0, 0.0, 0.0]), np.array([0.0, 1.0, 0.0])]
    Y = [np.array([2.0, 0.1, 0.3]), np.array([0.4, 3.0, 0.2])]
    direction = fc_exact.direction(np.array([1.0, 2.0, 3.0]), S, Y)
    np.testing.assert_allclose(np.column_stack(Y).T @ direction, 0.0, atol=2e-15)
