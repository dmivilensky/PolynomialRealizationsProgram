"""FC and one-correction RFC: current verified retained-window policies.

Sources: krylov/Methods/{FC,RFC,RetainedSolve,Windows,Protocol}.lean and
krylov.tex, Definition FC and RFC. The gate is the defect of the OLD retained
window, exactly as ``rfcCorrection`` and ``rfcCorrection_array`` specify.
The augmented matrix alone supplies the correction. No adaptive window
heuristic, repeated correction, or objective-decrease rejection remains.

The practical ``root`` search is explicitly approximate. The ``quadratic``
search uses a counted directional Hessian product. ``operator_cycle`` is a
separate literal simulation of the verified abstract information protocol.
"""

import numpy as np
from scipy.linalg import norm

from xrbench.methods._exactls import quadratic_ls, root_ls
from xrbench.methods._xr_model import latest


def _coordinates(S, Y):
    scales = np.array([norm(step, check_finite=False) for step in S])
    if np.any(scales == 0):
        raise np.linalg.LinAlgError("zero retained FC step")
    return np.column_stack(S) / scales, np.column_stack(Y) / scales


def direction(gradient, S, Y):
    """Literal windowDirection; invoked solves must exist, with no restart."""
    if not S:
        return -gradient.copy()
    steps, images = _coordinates(S, Y)
    return -gradient + steps @ np.linalg.solve(images.T @ steps, images.T @ gradient)


def canonical_defect(C):
    diagonal = np.diag(C)
    if np.any(diagonal <= 0) or not np.all(np.isfinite(C)):
        return np.inf
    root = np.sqrt(diagonal)
    normalized = C / root[:, None] / root[None, :]
    return float(np.linalg.norm(normalized - normalized.T, 2))


def correction_displacement(S, Y, d, z, post_gradient, *, gamma_gate=None):
    """One literal latest-model correction, with the verified OLD-window gate."""
    if not S:
        return np.zeros_like(d), False
    steps, images = _coordinates(S, Y)
    if not canonical_defect(steps.T @ images) < 1:
        return np.zeros_like(d), False
    dnorm = float(norm(d, check_finite=False))
    if not dnorm > 0:
        return np.zeros_like(d), False
    U = np.column_stack([steps, d / dnorm])
    Z = np.column_stack([images, z / dnorm])
    H = latest(U.T @ Z)
    if gamma_gate is not None:
        diagonal = np.diag(H)
        if np.any(diagonal <= 0):
            return np.zeros_like(d), False
        root = np.sqrt(diagonal)
        if np.linalg.eigvalsh(H / root[:, None] / root[None, :])[0] < gamma_gate:
            return np.zeros_like(d), False
    # No positivity assumption is added to ordinary RFC: the definition
    # requires an invertible solve, and the gated RFC variant checks it above.
    return -U @ np.linalg.solve(H, U.T @ post_gradient), True


def step(
    O,
    x,
    g,
    state,
    iteration,
    *,
    correction=False,
    memory=None,
    cycle=None,
    search="root",
    root_rtol=1e-13,
    gamma_gate=None,
):
    S, Y = state.setdefault("S", []), state.setdefault("Y", [])
    if cycle is not None and iteration % cycle == 0:
        S.clear()
        Y.clear()
    if memory is not None:
        del S[: max(0, len(S) - memory)]
        del Y[: max(0, len(Y) - memory)]
    d = direction(g, S, Y)
    observation = (
        quadratic_ls(O, x, d, g)
        if search == "quadratic"
        else root_ls(O, x, d, g, state.get("alpha", 1.0), root_rtol)
    )
    if observation is None:
        return None
    alpha, xp, gp, fp, z = observation
    xn, gn = xp, gp
    if correction:
        displacement, applied = correction_displacement(S, Y, d, z, gp, gamma_gate=gamma_gate)
        if applied:
            # RFC's correction is evaluated without an extra f-decrease gate.
            xn = xp + displacement
            _, gn = O.fg(xn)
            state["corrections"] = state.get("corrections", 0) + 1
    S.append(xn - x)
    Y.append(gn - g)
    state["alpha"] = alpha
    return xn, gn


def solve(
    O,
    x0,
    *,
    correction=False,
    memory=None,
    cycle=None,
    search="root",
    root_rtol=1e-13,
    gamma_gate=None,
):
    if search not in {"root", "quadratic"}:
        raise ValueError("search must be explicitly root or quadratic")
    if memory is not None and memory < 1 or cycle is not None and cycle < 1:
        raise ValueError("memory/cycle must be positive")
    if gamma_gate is not None and not 0 < gamma_gate < 1:
        raise ValueError("gated RFC requires 0 < gamma_gate < 1")
    state = {}
    O.note(
        "search",
        dict(
            kind=search,
            root_rtol=root_rtol if search == "root" else None,
            hvp_counted=search == "quadratic",
        ),
    )
    try:
        _, g = O.fg(x0)
        x, iteration = np.asarray(x0, float).copy(), 0
        while np.any(g != 0):
            out = step(
                O,
                x,
                g,
                state,
                iteration,
                correction=correction,
                memory=memory,
                cycle=cycle,
                search=search,
                root_rtol=root_rtol,
                gamma_gate=gamma_gate,
            )
            if out is None:
                O.note("stop", "directional_search_failure")
                break
            x, g = out
            iteration += 1
            O.mark_iter()
    except np.linalg.LinAlgError as error:
        O.note("stop", "undefined_theoretical_solve")
        O.note("detail", str(error))
    finally:
        O.note("corrections", state.get("corrections", 0))


def operator_cycle(
    search_operators,
    correction_operators,
    initial_gradient,
    *,
    correction=False,
    memory=None,
    gamma_gate=None,
):
    """Literal finite ``methodRun`` simulation with separately observed A_k d.

    This is an operator-model mechanism experiment, not optimization of a
    fixed nonlinear objective. Operators are used only to answer their
    prescribed current probe/correction query; decisions use observed vectors.
    A final correction is left unevaluated and reported separately.
    """
    g = np.asarray(initial_gradient, float).copy()
    x, S, Y, records = np.zeros_like(g), [], [], []
    count = len(search_operators)
    if len(correction_operators) != count:
        raise ValueError("one correction operator is required per search operator")
    for k, (A, B) in enumerate(zip(search_operators, correction_operators)):
        if memory is not None:
            S, Y = S[-memory:], Y[-memory:]
        d = direction(g, S, Y)
        z = np.asarray(A) @ d
        alpha = -float(g @ d) / float(d @ z)
        post = g + alpha * z
        move, applied = (
            correction_displacement(S, Y, d, z, post, gamma_gate=gamma_gate)
            if correction
            else (np.zeros_like(g), False)
        )
        total = alpha * d + move
        terminal = k == count - 1
        output_gradient = post + np.asarray(B) @ move
        records.append(
            dict(
                direction=d.copy(),
                probe=z.copy(),
                alpha=alpha,
                searched_gradient=post.copy(),
                correction=move.copy(),
                gradient=output_gradient.copy(),
                point=(x + total).copy(),
                correction_evaluated=bool(applied and not terminal),
                final_virtual=bool(applied and terminal),
            )
        )
        S.append(total)
        Y.append(output_gradient - g)
        x, g = x + total, output_gradient
    return records
