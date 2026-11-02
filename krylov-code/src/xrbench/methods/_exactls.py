"""Search oracles for theoretical controls; numerical roots are not exact searches.

The abstract verified FC/RFC model observes z=A_k d and takes the algebraic
length -g^T d/(d^T z). For a fixed quadratic, ``quadratic_ls`` realizes that
length with an explicitly counted Hessian-vector query. ``root_ls`` instead
solves the directional derivative to a declared tolerance and counts every
actual endpoint query. These information/cost conventions must not be mixed.
"""

import numpy as np
from scipy.optimize import brentq


def quadratic_ls(O, x, d, g):
    """Analytic quadratic line minimizer, including its actual endpoint query."""
    problem = O.p
    declared = getattr(problem, "meta", {}).get("convex_quadratic", False)
    # Independent test fixtures may expose an explicit fixed quadratic matrix.
    declared = declared or isinstance(getattr(problem, "A", None), np.ndarray)
    if not declared or not hasattr(problem, "hvp"):
        raise ValueError("analytic quadratic search requires a declared fixed quadratic and HVP")
    z = O.hvp(x, d)
    curvature = float(d @ z)
    slope = float(g @ d)
    if not curvature > 0 or not slope < 0:
        return None
    alpha = -slope / curvature
    xt = x + alpha * d
    ft, gt = O.fg(xt)
    if not np.isfinite(ft) or not np.all(np.isfinite(gt)):
        return None
    return alpha, xt, gt, ft, z


def root_ls(O, x, d, g, initial=1.0, rtol=1e-13):
    """Counted directional-derivative root; no mathematical exactness claim."""
    scale = float(np.max(np.abs(d)))
    if not np.isfinite(scale) or not scale > 0:
        return None
    unit = d / scale
    initial_derivative = float(g @ unit)
    if not initial_derivative < 0 or not np.isfinite(initial_derivative):
        return None
    cache = {}

    def derivative(length):
        if length not in cache:
            ft, gt = O.fg(x + length * unit)
            cache[length] = float(gt @ unit), gt, ft
        return cache[length][0]

    lo, hi = 0.0, float(initial) * scale
    if not np.isfinite(hi) or not hi > 0:
        hi = max(1.0, float(np.max(np.abs(x))))
    for _ in range(2048):
        value = derivative(hi)
        if not np.isfinite(value):
            hi = lo + (hi - lo) / 2
            if hi == lo:
                return None
        elif value >= 0:
            break
        else:
            lo, hi = hi, 2 * hi
            if not np.isfinite(hi):
                return None
    else:
        return None
    if abs(value) <= rtol * abs(initial_derivative):
        length = hi
    else:
        try:
            length = brentq(
                lambda t: initial_derivative if t == 0 else derivative(t),
                lo,
                hi,
                xtol=np.nextafter(0.0, 1.0),
                rtol=rtol,
                maxiter=256,
            )
        except (ValueError, RuntimeError):
            return None
    alpha = length / scale
    xt = x + length * unit
    if not alpha > 0 or not np.isfinite(alpha) or np.array_equal(xt, x):
        return None
    derivative(length)
    _, gt, ft = cache[length]
    if not np.isfinite(ft) or not np.all(np.isfinite(gt)):
        return None
    # The secant z is an averaged directional Hessian observation; its
    # equality to A_k d is the smooth-function interpretation of the model.
    return alpha, xt, gt, ft, (gt - g) / alpha
