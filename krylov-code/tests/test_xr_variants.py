"""Only the current, composable and explicitly named XR ablations remain."""

import numpy as np
import pytest
from _infra import Quad, run_gtol

from xrbench.methods import xr


@pytest.mark.parametrize(
    "kwargs",
    [
        {},
        {"values": True},
        {"m0": 5, "m_max": 5},
        {"values": True, "m0": 5, "m_max": 5},
        {"window": "positive"},
        {"probe": False},
        {"trial": "lagged"},
        {"values": True, "split": "euclidean"},
    ],
)
def test_supported_current_variants_reach_an_actual_gradient_target(kwargs):
    problem = Quad(n=16, kappa=100.0)
    result = run_gtol(xr.solve, problem, kwargs, budget=1000)
    assert result["status"] == "converged", result
    x = np.asarray(result["hit"]["x"])
    assert np.linalg.norm(problem.grad(x)) <= 1e-8 * np.linalg.norm(problem.grad(problem.x0))


def test_growing_window_updates_with_current_clean_counter():
    result = run_gtol(xr.solve, Quad(n=20, kappa=30.0), dict(m0=3, m_max=20, q=1))
    assert result["status"] == "converged"
    memory = result["info"]["growing_memory"]
    assert memory["maximum"] > 3 and memory["changes"] > 0


@pytest.mark.parametrize("kw", [{"feature": "base"}, {"cert": "diag"}, {"launch": "evaluated"}])
def test_removed_legacy_options_are_rejected(kw):
    with pytest.raises(TypeError):
        xr.solve(None, np.ones(2), **kw)
