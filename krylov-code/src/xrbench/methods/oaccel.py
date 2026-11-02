"""O-ACCEL: objective acceleration with the published CUTEst preconditioner B.

Source: A. N. Riseth, Objective acceleration for unconstrained optimization,
Numerical Linear Algebra with Applications 26(1), e2216 (2019),
https://doi.org/10.1002/nla.2216, https://arxiv.org/abs/1710.05200.
Author implementation: https://github.com/anriseth/objective_accel_code.

Equations (3), (10), (21) and (30) define the acceleration, coefficient
system, regularization and preconditioner B. Algorithm 1 defines the descent
check and window restart. Section 3.2 gives wmax=20, delta=1e-4, eps0=1e-12,
and More--Thuente c1=1e-4, c2=.1, starting at one with maxfev=20. Section 3.5
uses B for CUTEst; it is the default and sole primary registered preset.

Numerical implementation: form the identical coefficient system directly from
point/gradient differences (equation (10)), avoiding cancellation in expanded
inner products of equation (Algorithm 2). Form the accelerated displacement
before adding it to xP for the same reason. The Tikhonov shift uses the
Optim.jl floor eps0*max(max diag(A),eps0) so it remains positive at a zero or
negative diagonal. The More--Thuente solver is SciPy's MINPACK-2 DCSRCH port.
On a warning it returns the best sufficient-decrease trial, as the historical
LineSearches.jl implementation did; if none exists the acceleration is discarded
and the window restarts at xP. Nonfinite preconditioner trials are halved.
The shared oracle supplies stopping and budgets. An unchanged outer iterate
terminates, matching Optim.jl's zero absolute step tolerance.

Option A remains an explicit reference option for algebra tests; it is not
an additional primary competitor.
"""

import numpy as np
from scipy.optimize._dcsrch import DCSRCH

_ITERFINITEMAX = 52  # -log2(eps(Float64)), LineSearches static.jl L28 / morethuente.jl L176


def _more_thuente(O, x, f0, g0, d, stp, c1, c2, xtol, stpmin, stpmax, maxfev):
    """More-Thuente line search [MT] on phi(t) = f(x + t d) through scipy's MINPACK-2 dcsrch.

    Returns (t, x_t, f_t, g_t) or None (failure: no trial with sufficient decrease).  See D2, D3, D5.
    """
    dphi0 = float(g0 @ d)
    if not (np.isfinite(f0) and np.isfinite(dphi0)) or dphi0 >= 0.0:
        return None  # morethuente.jl L184-L195: not a descent direction
    ls = DCSRCH(None, None, c1, c2, xtol, stpmin, stpmax)
    stp = min(max(stp, stpmin), stpmax)  # morethuente.jl L231-L232
    stp, _, _, task = ls._iterate(stp, f0, dphi0, b"START")
    if task[:5] == b"ERROR":
        return None
    trials = []  # finite trials (t, x_t, f_t, g_t)

    def ev(t):
        xt = x + t * d
        ft, gt = O.fg(xt)
        dt = float(gt @ d)
        ok = np.isfinite(ft) and np.isfinite(dt)
        if ok:
            trials.append((t, xt, ft, gt))
        return xt, ft, gt, dt, ok

    def best_sufficient_decrease():  # D3: MINPACK "lowest point obtained so far"
        cand = [tr for tr in trials if tr[2] <= f0 + c1 * tr[0] * dphi0]
        if not cand:
            return None
        return min(cand, key=lambda tr: tr[2])

    # first trial; halve until finite (LineSearches morethuente.jl L233-L248)
    xt, ft, gt, dt, ok = ev(stp)
    nfev = 1
    it = 0
    while not ok and it < _ITERFINITEMAX:
        it += 1
        stp = 0.5 * stp
        xt, ft, gt, dt, ok = ev(stp)
        nfev += 1
    if not ok:
        return None
    while True:
        # dcsrch: test strong Wolfe [MT] (sufficient decrease f <= f0 + c1 t phi'(0),
        # curvature |phi'(t)| <= c2 |phi'(0)|), else update the interval of uncertainty and propose a trial
        stp_new, _, _, task = ls._iterate(stp, ft, dt, b"FG")
        if task[:4] == b"CONV":
            return stp, xt, ft, gt
        if task[:4] == b"WARN" or task[:5] == b"ERROR" or nfev >= maxfev:
            return best_sufficient_decrease()
        stp = stp_new
        xt, ft, gt, dt, ok = ev(stp)
        nfev += 1
        # non-finite trial: bisect toward the best step stx, shrink stpmax (morethuente.jl L306-L324)
        it = 0
        while not ok:
            if nfev >= maxfev or it >= _ITERFINITEMAX or stp == ls.stx:
                return best_sufficient_decrease()
            ls.stpmax = min(ls.stpmax, stp)
            it += 1
            stp = 0.5 * (stp + ls.stx)
            xt, ft, gt, dt, ok = ev(stp)
            nfev += 1


def _precondition(O, x, f, g, precond, delta, ls_kw):
    """Steepest-descent nonlinear preconditioner M(f, x) = x - lambda g/||g|| ([R] eqs. (29)/(30);
    [DS13] eqs. (2.1)/(2.2)).  Returns (x^P, f^P, g^P, moved)."""
    gn = float(np.linalg.norm(g))
    if precond == "A":
        # [R] eq. (29) / [DS13] eq. (2.1): lambda_A by More-Thuente, starting at lambda = 1 ([R] Sec. 3.2)
        res = _more_thuente(O, x, f, g, -g / gn, 1.0, **ls_kw)
        if res is None:  # D3: GradientDescent does not move (gradient_descent.jl L100-L116)
            return x, f, g, False
        _, xP, fP, gP = res
        return xP, fP, gP, True
    # precond == 'B': [R] eq. (30) / [DS13] eq. (2.2): lambda_B = min(delta, ||g||);
    # Optim.jl: GradientDescent(alphaguess=InitialStatic(alpha=delta, scaled=true), linesearch=Static())
    # (ngmres.jl L125-L129; initialguess.jl L21-L23: alpha = min(delta, ||s||)/||s|| on s = -g)
    a = min(delta, gn) / gn
    xP = x - a * g
    fP, gP = O.fg(xP)
    it = 0
    while (
        not np.isfinite(fP) and it < _ITERFINITEMAX
    ):  # Static: halve until f is finite (static.jl L26-L34)
        it += 1
        a *= 0.5
        xP = x - a * g
        fP = O.f(xP)
        if np.isfinite(fP):
            gP = O.g(xP)
    if not (np.isfinite(fP) and np.all(np.isfinite(gP))):
        return x, f, g, False  # D5: accept_step! rejects (gradient_descent.jl L126-L131)
    return xP, fP, gP, True


def solve(
    O,
    x0,
    nonlinear="oaccel",
    wmax=20,
    precond="B",
    delta=1e-4,
    eps0=1e-12,
    c1=1e-4,
    c2=None,
    maxfev=20,
    stpmin=1e-16,
    stpmax=65536.0,
    xtol=1e-8,
    trace=None,
):
    if nonlinear != "oaccel":
        raise ValueError("Only the O-ACCEL method is retained")
    if precond not in ("A", "B"):
        raise ValueError("precond must be 'A' or 'B'")
    if c2 is None:
        c2 = 0.1  # [R] Sec. 3.2
    ls_kw = dict(c1=c1, c2=c2, xtol=xtol, stpmin=stpmin, stpmax=stpmax, maxfev=maxfev)
    wmax = int(wmax)
    note = getattr(O, "note", None)  # optional oracle extension (diagnostics only)
    cnt = dict(restarts=0, ls_fail_acc=0, ls_fail_pre=0)

    def bump(key):
        cnt[key] += 1
        if note is not None:
            note(key, cnt[key])

    def stop(reason):
        if note is not None:
            note("stop", reason)

    x = np.array(x0, dtype=float)
    n = x.size
    f, g = O.fg(x)
    if not (np.isfinite(f) and np.all(np.isfinite(g))):
        stop("non-finite f or g at x0")
        return
    # window storage (ngmres.jl L247-L259; [R] Alg. 2: x_1 <- x, r_1 <- g(x), q_11)
    X = np.full((n, wmax), np.nan)
    R = np.full((n, wmax), np.nan)
    X[:, 0] = x
    R[:, 0] = g
    curw, k = 1, 0

    while True:
        x_prev0 = x  # ngmres.jl L380-L381 (for the x_abstol = 0 test, D4)
        k += 1  # ngmres.jl L383
        # ---- Step 1: preconditioner x^P = M(f, x_k)  ([R] Alg. 1; ngmres.jl L386-L391)
        if not np.any(g):
            stop("g = 0")
            return  # g = 0 exactly: stationary, M undefined
        xP, fP, gP, moved = _precondition(O, x, f, g, precond, delta, ls_kw)
        if not moved:
            bump("ls_fail_pre")  # D3/D5: preconditioner did not move, x^P = x_k
        if not (np.isfinite(fP) and np.all(np.isfinite(gP))):
            stop("non-finite preconditioner point")
            return  # ngmres.jl L393-L396
        # ---- Step 2: acceleration system ([R] Alg. 2; ngmres.jl L407-L421)
        Xw, Rw = X[:, :curw], R[:, :curw]
        # Equation (10), assembled from differences to retain translation
        # invariance numerically when iterates have a large common offset.
        D = Xw - xP[:, None]
        E = Rw - gP[:, None]
        A = D.T @ E
        b = -(D.T @ gP)
        # Tikhonov shift ([R] eq. (21); [DS12] Sec. 2.1; ngmres.jl L428, deviation D6)
        eps = eps0 * max(float(np.max(np.diag(A))), eps0)
        try:
            alpha = np.linalg.solve(A + eps * np.eye(curw), b)  # ngmres.jl L429-L435
        except np.linalg.LinAlgError:
            alpha = np.full(curw, np.nan)
        restart = False
        xA = None
        if np.any(np.isnan(alpha)):
            s = np.zeros(n)  # ngmres.jl L436-L439: alpha NaN -> restart
            restart = True
        else:
            # x^A = x^P + sum_j alpha_j (x_j - x^P)  ([R] eq. (3); [DS13] eq. (2.3); ngmres.jl L441-L443)
            s = D @ alpha
            xA = xP + s
        # ---- Step 3: descent test and line search ([R] Alg. 1; [DS12] Sec. 2.1; ngmres.jl L448-L500)
        sTg = float(s @ gP)
        ls_ok = False
        if sTg >= 0.0 or not np.isfinite(sTg):
            restart = True  # not a descent direction: x_{k+1} = x^P, reset window
            x, f, g = xP, fP, gP
        else:
            res = _more_thuente(
                O, xP, fP, gP, s, 1.0, **ls_kw
            )  # InitialStatic() alpha = 1 (ngmres.jl L123)
            if res is not None:
                _, x, f, g = res
                ls_ok = True
            else:  # ngmres.jl L491-L499: discard x^A, restart at x^P
                bump("ls_fail_acc")
                restart = True
                x, f, g = xP, fP, gP
        if restart:
            bump("restarts")
        O.mark_iter()
        if trace is not None:
            trace.append(
                dict(
                    x_P=xP.copy(),
                    x_A=None if xA is None else xA.copy(),
                    x=x.copy(),
                    restart=restart,
                    curw=curw,
                    ls_ok=ls_ok,
                )
            )
        # ---- Step 4: window update (update_fgh!, ngmres.jl L511-L534; [R] Alg. 2)
        if restart:
            k = 0  # ngmres.jl L518-L520: reset history to {x}
            curw = 1
        else:
            curw = min(curw + 1, wmax)  # ngmres.jl L522
        j = k % wmax  # j = mod(k, wmax) + 1 (1-based), ngmres.jl L524
        X[:, j] = x
        R[:, j] = g
        # D4: Optim.jl default x_abstol = 0 (assess_convergence.jl L66): x unchanged -> stop
        if np.array_equal(x, x_prev0):
            stop("x unchanged over an iteration (Optim.jl x_abstol = 0)")
            return
