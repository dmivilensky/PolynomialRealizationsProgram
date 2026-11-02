"""BFGS-SP: dense BFGS with Shanno-Phua initial scaling and the More-Thuente line search.

Sources: D. F. Shanno, K. H. Phua, "Matrix conditioning and nonlinear optimization", Math. Program. 14 (1978)
149-160 (initial scaling H0 = (s'y/y'y) I applied before the first update; Nocedal-Wright 2006 eq. (6.20));
J. J. More, D. J. Thuente, "Line search algorithms with guaranteed sufficient decrease", ACM TOMS 20 (1994)
286-307 (MINPACK-2 dcsrch, used through scipy.optimize._linesearch.line_search_wolfe1); BFGS inverse update
(Nocedal-Wright eq. (6.17)).  Code ported from code/methods2.py::bfgs_wolfe and ::wolfe_ls / ::_wolfe_bisect.
Settings (as in methods2): strong Wolfe c1 = 1e-4, c2 = 0.9; dcsrch with amax = 1e8, amin = 1e-12, xtol = 1e-14;
first trial step 1/||g0||_inf, unit step afterwards; if dcsrch fails, a bisection zoom (Nocedal-Wright Alg. 3.5/3.6);
if that fails along the BFGS direction, a steepest-descent retry with H reset.
Deviations from methods2.bfgs_wolfe:
  * update skipped when s'y <= skip_rel ||s|| ||y|| (skip_rel = 1e-10, as required by v5/BENCH_PLAN.md B2);
    methods2 skipped only when s'y <= 1e-300.  (With the Wolfe conditions s'y > 0 always; the test only matters
    after the fallback search.)
  * the update (I - rho s y')H(I - rho y s') + rho s s' is evaluated in the expanded O(n^2) form
    H - rho (s (Hy)' + (Hy) s') + (rho^2 y'Hy + rho) s s' (methods2 formed the O(n^3) product);
  * f at the current point is carried from the previous line search (methods2 re-evaluated O.f(x) uncounted);
  * methods2.wolfe_ls wrapped dcsrch in `except Exception` (which would swallow the oracle's stop signals): only
    numerical exceptions (ValueError, ArithmeticError, LinAlgError) are caught here.
Restricted to n <= 3000 by the registry (O(n^2) memory and time per iteration).
"""

import numpy as np
from scipy.optimize._linesearch import line_search_wolfe1


def _make_fg(O):
    cache = {}

    def fg(xx):
        key = xx.tobytes()
        if key not in cache:
            f = O.f(xx)
            cache[key] = (f, O.g(xx) if np.isfinite(f) else np.full_like(xx, np.nan))
        return cache[key]

    return fg


def wolfe_ls(O, x, d, f0, g0, a0, c1=1e-4, c2=0.1, maxit=60):
    """Strong Wolfe line search: MINPACK dcsrch (More-Thuente) through scipy on the direction scaled so that the
    initial trial step is a0; falls back to a bisection zoom.  Returns (a, x_new, f_new, g_new) or None."""
    fg = _make_fg(O)
    p = a0 * d
    try:
        res = line_search_wolfe1(
            lambda xx: fg(xx)[0] if np.isfinite(fg(xx)[0]) else 1e300,
            lambda xx: fg(xx)[1] if np.isfinite(fg(xx)[0]) else np.full_like(xx, 0.0),
            x,
            p,
            gfk=g0,
            old_fval=f0,
            c1=c1,
            c2=c2,
            amax=1e8,
            amin=1e-12,
        )
        t = res[0]
    except (ValueError, ArithmeticError, np.linalg.LinAlgError):
        t = None
    if t is not None and np.isfinite(t) and t > 0 and not np.array_equal(x + t * p, x):
        xn = x + t * p
        fn, gn = fg(xn)
        slope = float(g0 @ d)
        if (
            np.isfinite(fn)
            and np.all(np.isfinite(gn))
            and slope < 0
            and fn <= f0 + c1 * t * a0 * slope
            and abs(gn @ d) <= -c2 * slope
        ):
            return t * a0, xn, fn, gn
    return _wolfe_bisect(O, x, d, f0, g0, a0, c1, c2, maxit)


def _wolfe_bisect(O, x, d, f0, g0, a0, c1=1e-4, c2=0.1, maxit=60):
    """Strong Wolfe line search (Nocedal-Wright Alg. 3.5/3.6, bisection zoom).  Returns (a, x_new, f_new, g_new)."""
    dg0 = g0 @ d
    if dg0 >= 0:
        return None
    cache = {}

    def phi(a):
        if not (np.isfinite(a) and a > 0) or np.array_equal(x + a * d, x):
            return np.inf, np.full_like(g0, np.nan), np.nan
        if a not in cache:
            xx = x + a * d
            f = O.f(xx)
            g = O.g(xx) if np.isfinite(f) else np.full_like(x, np.nan)
            cache[a] = (f, g, (g @ d) if np.isfinite(f) else np.nan)
        return cache[a]

    def zoom(lo, hi, flo, dlo):
        for _ in range(maxit):
            a = 0.5 * (lo + hi)
            if a == lo or a == hi:
                return None
            f, g, dg = phi(a)
            if not np.isfinite(f) or not np.isfinite(dg) or f > f0 + c1 * a * dg0 or f >= flo:
                hi = a
            else:
                if abs(dg) <= -c2 * dg0:
                    return a
                if dg * (hi - lo) >= 0:
                    hi = lo
                lo, flo = a, f
            if abs(hi - lo) < 1e-16 * max(abs(lo), abs(hi), np.finfo(float).tiny):
                return None
        return None

    ap, fp, dp = 0.0, f0, dg0
    a = a0
    for i in range(maxit):
        f, g, dg = phi(a)
        if not np.isfinite(f) or not np.isfinite(dg):
            a = 0.5 * (ap + a)
            continue
        if f > f0 + c1 * a * dg0 or (i > 0 and f >= fp):
            a = zoom(ap, a, fp, dp)
            break
        if abs(dg) <= -c2 * dg0:
            break
        if dg >= 0:
            a = zoom(a, ap, f, dg)
            break
        ap, fp, dp = a, f, dg
        a = 2.0 * a
    if a is None or a <= 0:
        return None
    f, g, dg = phi(a)
    if (
        np.isfinite(f)
        and np.all(np.isfinite(g))
        and f <= f0 + c1 * a * dg0
        and abs(dg) <= -c2 * dg0
    ):
        return a, x + a * d, f, g
    return None


def solve(O, x0, c1=1e-4, c2=0.9, skip_rel=1e-10):
    n = len(x0)
    f, g = O.fg(x0)
    x, H = x0.copy(), None
    nskip = 0
    try:
        while True:
            d = -g if H is None else -H @ g
            a0 = 1.0 if H is not None else 1.0 / max(np.max(np.abs(g)), 1e-300)
            r = wolfe_ls(O, x, d, f, g, a0, c1=c1, c2=c2)
            if r is None:
                d = -g
                r = wolfe_ls(O, x, d, f, g, 1.0 / max(np.max(np.abs(g)), 1e-300), c1=c1, c2=c2)
                if r is None:
                    O.note("stop", "line_search_failed")
                    return
                H = None
            a, xn, fn, gn = r
            s = xn - x
            y = gn - g
            sy = s @ y
            if sy > skip_rel * np.linalg.norm(s) * np.linalg.norm(y):
                if H is None:
                    H = (sy / (y @ y)) * np.eye(n)  # Shanno-Phua scaling (NW eq. 6.20)
                rho = 1 / sy
                Hy = H @ y  # BFGS inverse update (NW eq. 6.17),
                H -= rho * (np.outer(s, Hy) + np.outer(Hy, s))  # expanded to O(n^2) work
                H += (rho * rho * (y @ Hy) + rho) * np.outer(s, s)
            else:
                nskip += 1
            x, f, g = xn, fn, gn
            O.mark_iter()
    finally:
        O.note("nskip", nskip)
