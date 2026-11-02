"""Minimal theoretical XRFC executor, with no practical legacy safeguards.

Source: krylov.tex, eq:virtual-launch; Lean OneGradient.xrfcMethod and
XRFC.xrfc_full_reference. Every actual trial is prescribed from observed data;
the returned virtual point is unevaluated. Singular required solves are an
explicit domain failure, never a hidden restart or a different algorithm.
"""

import numpy as np

from xrbench.methods._xr_model import latest
from xrbench.methods.fc_exact import _coordinates


def virtual_model(x, g, S, Y):
    if not S:
        return x.copy(), g.copy(), -g.copy()
    steps, images = _coordinates(S, Y)
    C = steps.T @ images
    w = -np.linalg.solve(latest(C), steps.T @ g)
    xv, gv = x + steps @ w, g + images @ w
    d = -gv + steps @ np.linalg.solve(C.T, images.T @ gv)
    return xv, gv, d


def advance(O, x, g, state, iteration, *, trial=1.0, memory=None):
    """One observed gradient, followed by a free unevaluated virtual output."""
    S, Y = state.setdefault("S", []), state.setdefault("Y", [])
    if memory is not None:
        del S[: max(0, len(S) - memory)]
        del Y[: max(0, len(Y) - memory)]
    xv, gv, d = virtual_model(x, g, S, Y)
    observed = dict(
        iteration=iteration,
        point=x,
        gradient=g,
        S=S,
        Y=Y,
        virtual_point=xv,
        virtual_gradient=gv,
        direction=d,
    )
    tau = float(trial(observed) if callable(trial) else trial)
    if not np.isfinite(tau) or tau == 0:
        raise ValueError("the theoretical XRFC trial must be finite and nonzero")
    xt = xv + tau * d
    _, gt = O.fg(xt)
    S.append(xt - x)
    Y.append(gt - g)
    if memory is not None:
        del S[: max(0, len(S) - memory)]
        del Y[: max(0, len(Y) - memory)]
    output, model_gradient, _ = virtual_model(xt, gt, S, Y)
    state["output"] = output.copy()
    state["model_gradient"] = model_gradient.copy()
    return xt, gt, output, model_gradient


def solve(O, x0, *, trial=1.0, memory=None, steps=None, hook=None):
    """Finite theoretical cycle; a virtual output never claims an observed hit."""
    if memory is not None and memory < 1:
        raise ValueError("memory must be positive")
    count = len(x0) if steps is None else int(steps)
    if count < 0 or count > len(x0):
        raise ValueError("the theoretical cycle length must lie between zero and dimension")
    state = {}
    try:
        _, g = O.fg(x0)
        x = np.asarray(x0, float).copy()
        for iteration in range(count):
            x, g, output, model_gradient = advance(
                O, x, g, state, iteration, trial=trial, memory=memory
            )
            if hook is not None:
                hook(output.copy(), model_gradient.copy(), iteration + 1)
            O.mark_iter()
        O.note("stop", "theoretical_cycle_complete")
    except np.linalg.LinAlgError as error:
        O.note("stop", "undefined_theoretical_solve")
        O.note("detail", str(error))
    finally:
        if "output" in state:
            O.note(
                "virtual_output",
                dict(
                    point=state["output"].tolist(),
                    model_gradient_norm=float(np.linalg.norm(state["model_gradient"])),
                    evaluated=False,
                ),
            )


def operator_cycle(operators, initial_gradient, *, trial=1.0, memory=None, output_operator=None):
    """Literal one-gradient operator execution; output operator is diagnostic only."""
    g, x = np.asarray(initial_gradient, float).copy(), np.zeros_like(initial_gradient, dtype=float)
    S, Y, records = [], [], []
    for iteration, A in enumerate(operators):
        if memory is not None:
            S, Y = S[-memory:], Y[-memory:]
        xv, gv, d = virtual_model(x, g, S, Y)
        observed = dict(
            iteration=iteration,
            point=x,
            gradient=g,
            S=S,
            Y=Y,
            virtual_point=xv,
            virtual_gradient=gv,
            direction=d,
        )
        tau = float(trial(observed) if callable(trial) else trial)
        if tau == 0 or not np.isfinite(tau):
            raise ValueError("nonzero finite trial required")
        xt = xv + tau * d
        step = xt - x
        gt = g + np.asarray(A) @ step
        S.append(step)
        Y.append(gt - g)
        output, model_g, _ = virtual_model(xt, gt, S, Y)
        record = dict(
            point=xt.copy(),
            gradient=gt.copy(),
            output=output.copy(),
            model_gradient=model_g.copy(),
            trial=tau,
            output_evaluated=False,
        )
        if output_operator is not None:
            # This quantity is available only to the external evaluator, and
            # is never used by the next algorithm decision.
            record["semantic_output_gradient"] = gt + np.asarray(output_operator) @ (output - xt)
        records.append(record)
        x, g = xt, gt
    return records
