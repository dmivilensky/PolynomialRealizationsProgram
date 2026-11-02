"""Practical XR / XR-F with a fresh secant scale and explicit diagnostic policies.

Sources: krylov.tex, Algorithms ModelStep and XR; Lean modules AlgorithmState,
AlgorithmModel and Execution. See docs/AlgorithmCorrespondence.md for the exact
mapping and explicit floating-point policies. The shared virtual model,
window, F gates and memory controller retain their mathematical contracts.
The midpoint policy is an explicit Ritz/Schur diagnostic, not the default.
"""

import math

import numpy as np
from scipy.linalg import norm

from xrbench.methods._xr_model import (
    Pair,
    Parameters,
    State,
    latest,
    model_step,
    trapezoid_defect,
    update_capacity,
)

__all__ = ["solve", "iterate", "Pair", "Parameters", "State", "model_step", "latest"]


def initialize(O, x0, params, mu=None, L=None):
    """Cache the actual initial observation; no Hessian information is inferred."""
    f, g = O.fg(x0)
    if not math.isfinite(f) or not np.all(np.isfinite(g)):
        raise ValueError("XR requires a finite initial value and gradient")
    size = float(np.max(np.abs(g)))
    tau0 = 1.0 if size == 0 else 1 / size
    bounds = None
    if mu is not None or L is not None:
        if mu is None or L is None or not 0 < mu <= L or not math.isfinite(L):
            raise ValueError("initial spectral estimates require finite 0 < mu <= L")
        bounds = (float(mu), float(L))
    capacity = min(len(x0), params.m0)
    return State(
        np.asarray(x0, float).copy(),
        float(f),
        np.asarray(g, float).copy(),
        capacity,
        tau0,
        params.epsilon * tau0,
        tau0 / params.epsilon,
        bounds=bounds,
        secant_curvature=1 / tau0,
        maximum_capacity=capacity,
    )


def _chi(f, ft, slope):
    """Curvature ratio of the actual trial, with finite checks before division."""
    if not math.isfinite(ft) or not math.isfinite(slope) or not slope < 0:
        return math.inf
    try:
        residual = math.fsum((ft, -f, -slope))
    except OverflowError:
        return math.inf
    value = 2 * (residual / -slope)
    return value if math.isfinite(value) else math.inf


def _learn_lagged_curvature(state, model, point, gradient, length):
    """Learn only from the genuine unshortened, unsafeguarded model launch.

    On a quadratic, g_t-g_virtual=A(x_t-x_virtual). Projecting both vectors
    on the unit model direction gives its true Rayleigh quotient, including
    the actual trial coefficient. A shortened whole-step launch also scales
    the projection correction and does not satisfy this identity.
    """
    if length != 1.0 or model.safeguarded:
        return
    size = float(norm(model.direction, check_finite=False))
    if not size > 0 or not math.isfinite(size):
        return
    unit = model.direction / size
    displacement = float(unit @ (point - model.virtual_x))
    if displacement == 0 or not math.isfinite(displacement):
        return
    estimate = float(unit @ (gradient - model.virtual_g)) / displacement
    if estimate > 0 and math.isfinite(estimate):
        state.lagged = estimate


def iterate(O, state, params, *, maxbt=80, hook=None, trace=None):
    """One accepted outer advance, with at most one finite rejected probe.

    The finite evaluation limit is an execution stop, never a replacement
    acceptance rule. Oracle budget/time/convergence exceptions propagate.
    """
    first = current = model_step(state, params, hook)
    probed, length = False, 1.0
    for evaluations in range(1, maxbt + 1):
        step = length * current.u
        xt = state.x + step
        # Store the displacement to the actual representable oracle point.
        # Over the reals this equals length*u; near rounding, using the
        # intended vector would pair a different step with the observed y.
        step = xt - state.x
        if np.array_equal(xt, state.x):
            O.note("stop", "floating_point_stagnation")
            return False
        # A first rejected probe needs its gradient. Once that observation
        # is available, later rejected Armijo trials need only f. The shared
        # oracle counts a gradient only when it is actually requested.
        if params.probe and not probed:
            ft, gt = O.fg(xt)
        else:
            ft, gt = O.f(xt), None
        finite_value = math.isfinite(ft)
        slope = float(state.g @ step)
        chi = _chi(state.f, ft, slope) if finite_value else math.inf
        # Lean's accepted_iff_armijo proves this is the same real predicate.
        # Evaluating it directly avoids cancellation in chi near a flat
        # rounded objective, without an epsilon relaxation or extra query.
        armijo = bool(finite_value and slope < 0 and ft <= state.f + params.sigma * slope)
        if armijo and gt is None:
            gt = O.g(xt)
        finite_gradient = gt is not None and bool(np.all(np.isfinite(gt)))
        if gt is not None and not finite_gradient:
            # A scalar acceptance cannot accept a nonfinite gradient or
            # turn it into a positive-curvature observation.
            chi = math.inf
        accepted = armijo and finite_gradient
        informative = finite_value and finite_gradient and chi < math.inf
        if trace is not None:
            trace.append(
                dict(
                    iteration=state.iteration,
                    evaluation=evaluations,
                    value=float(ft),
                    slope=slope,
                    chi=chi,
                    accepted=bool(accepted),
                    window=len(state.pairs),
                    capacity=state.capacity,
                    gradient_evaluated=gt is not None,
                )
            )
        if informative and (accepted or (params.probe and not probed)):
            image = gt - state.g
            delta = (
                trapezoid_defect(state.f, ft, state.g, gt, step, params.noise_multiplier)
                if params.values
                else 0.0
            )
            pair = Pair.observe(step, image, delta)
            if pair is not None:
                state.pairs.append(pair)
                state.secant_curvature = float(pair.s @ pair.y)
            else:
                state.counters["nskip"] += 1
            if params.trial == "lagged":
                _learn_lagged_curvature(state, current, xt, gt, length)
        if accepted:
            for pair in state.pairs:
                pair.transport(step)
            previous = state.capacity
            state.capacity, state.clean = update_capacity(
                params,
                len(state.x),
                state.capacity,
                state.clean,
                first.first_pairs,
                first.deleted,
                evaluations,
            )
            state.memory_changes += int(previous != state.capacity)
            state.maximum_capacity = max(state.maximum_capacity, state.capacity)
            state.x, state.f, state.g = xt, float(ft), np.asarray(gt, float).copy()
            state.iteration += 1
            return True
        state.counters["nrej"] += 1
        if informative and params.probe and not probed:
            probed = True
            state.counters["nprobe"] += 1
            current = model_step(state, params, hook)
            length = 1.0
        else:
            length /= min(max(chi, 2.0), 10.0)
            state.counters["nbt"] += 1
    O.note("stop", "backtracking_limit")
    return False


def solve(
    O,
    x0,
    *,
    values=False,
    m0=10,
    m_max=100,
    q=3,
    inflation=2.0,
    theta=1.0,
    sigma=1e-4,
    epsilon=1e-10,
    eta0=1e-2,
    mu=None,
    L=None,
    window="hermitian",
    probe=True,
    trial="secant",
    split="model",
    floor=False,
    maxbt=80,
    noise_multiplier=100.0,
    rank_multiplier=32.0,
    safeguard=True,
    hook=None,
    trace=None,
):
    """Run the current XR algorithm (``values=True`` selects XR-F).

    Growth, a fresh positive observed secant scale and F are composable.
    The default does not compute Ritz values, Schur intervals or running
    spectral bounds. Set trial='midpoint', floor=True for that diagnostic.
    Set m0=m_max for
    fixed memory, or both to dimension for full memory. Nondefault window,
    probe/trial/split/floor options are the named scientific ablations; disabling
    the safeguard is reserved for conditional exact-quadratic identity tests.
    """
    params = Parameters(
        m0=m0,
        m_max=m_max,
        q=q,
        inflation=inflation,
        theta=theta,
        sigma=sigma,
        epsilon=epsilon,
        eta0=eta0,
        values=values,
        window=window,
        probe=probe,
        trial=trial,
        split=split,
        floor=floor,
        noise_multiplier=noise_multiplier,
        rank_multiplier=rank_multiplier,
        safeguard=safeguard,
    )
    params.validate(len(x0))
    state = None
    try:
        state = initialize(O, x0, params, mu, L)
        while np.any(state.g != 0):
            if not iterate(O, state, params, maxbt=maxbt, hook=hook, trace=trace):
                break
            O.mark_iter()
    except (np.linalg.LinAlgError, FloatingPointError) as error:
        O.note("stop", "numerical_linear_algebra")
        O.note("detail", str(error))
        if state is not None:
            state.counters["nnumerical"] += 1
    finally:
        if state is not None:
            O.note("counters", state.counters)
            O.note("mean_window", state.window_sum / max(state.model_calls, 1))
            O.note("maximum_window", state.max_window)
            O.note(
                "growing_memory",
                dict(
                    final=state.capacity,
                    maximum=state.maximum_capacity,
                    changes=state.memory_changes,
                    clean=state.clean,
                ),
            )
            O.note("spectral_estimates", state.bounds)
            O.note("secant_curvature", state.secant_curvature)
