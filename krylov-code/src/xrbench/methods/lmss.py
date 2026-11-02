"""Multipoint symmetric secant models and trust-region optimizers.

Primary preset: SC-INF-D with m=3 model pairs and q=5 curvature observations,
Brust, Erway and Marcia, Shape-changing trust-region methods using multipoint
symmetric secant matrices, Optim. Methods Softw. 39(5) (2024), 990--1007,
https://doi.org/10.1080/10556788.2023.2296441,
https://arxiv.org/abs/2209.12057. Compact model (15), shape subproblem
(19)--(22), initialization (31) and Section 4 default m,q are implemented.
The SC path retains every finite nonzero observation, including rejected trials,
and selects independent step columns for each compact model.

Additional algebra sources used in function comments:
[B83] Burdakov, Methods of the secant type for systems of equations with symmetric
Jacobian matrix, Numer. Funct. Anal. Optim. 6 (1983), 183--195.
[BMP] Burdakov, Martinez and Pilotta, A limited-memory multipoint symmetric secant
method for bound constrained optimization, Ann. Oper. Res. 117 (2002), 51--70.
[ER] Erway and Rezapour, A new multipoint symmetric secant method with a dense
initial matrix, https://arxiv.org/abs/2107.06321. The Euclidean reference path
uses Algorithms 1--2, the dense initialization Option 4, and the published
positive-curvature pair filter (27). Its sigma-regular pair selector is BMP's
numerical alternative to ER's unspecified dependence threshold.
[BEM] Brust, Erway and Marcia, On solving L-SR1 trust-region subproblems,
Comput. Optim. Appl. 66 (2017), 245--266,
https://doi.org/10.1007/s10589-016-9868-3 (Euclidean OBS subproblem).

Pairs are oldest first. Consequently the projected latest-information matrix
uses the upper triangle of S.T Y, whereas the compact correction uses its lower
triangle. Normalizing each pair by ||s|| does not change either matrix.
Pivoted QR discards numerical dependence at relative tolerance 1e-10; no
positive-definiteness modification is applied to trust-region models.

The SC outer loop follows SC-SR1 (2022), Algorithm 5, as cited by the MSS paper:
https://arxiv.org/abs/1607.03533, https://doi.org/10.1145/3550269.
The initial search follows the author LMSS_SC defaults: More--Thuente
c1=1e-4,c2=.9, alpha0=1, xtol=1e-6, stpmax=5, maxfev=3000. The initial
radius is twice the first step norm, followed by the published ratio/radius
constants. Shared-oracle stopping replaces the papers' different gradient
thresholds. The machine-radius stop is made relative to max(1,||x||_2).
The unregistered LS path is an algebra reference, not the published MSS solver.
"""

import math

import numpy as np
import scipy.linalg as sla
from scipy.optimize._dcsrch import DCSRCH

_EPS = np.finfo(float).eps


# ----------------------------------------------------------------------------- MSS algebra
def tbar(S, Y):
    """Latest-information matrix (oldest first): Tbar_ij = s_min(i,j)^T y_max(i,j) = sym(S^T Y) of [B83] (2.7)."""
    M = S.T @ Y
    return np.triu(M) + np.triu(M, 1).T


def mss_compact(S, Y, B0):
    """Dense MSS matrix from the compact form [ER] (8)/(14): B = B0 + Psi M Psi^T, Psi = [S, Y - B0 S],
    M = [[W (S^T B0 S - X) W, W], [W, 0]], W = (S^T S)^{-1}, X = sym(Y^T S) (newest first) = tril part here.
    For tests and small n only."""
    MY = S.T @ Y
    X = np.tril(MY) + np.tril(MY, -1).T  # [BMP] (26) / [ER] (8): T + E + T^T
    W = np.linalg.inv(S.T @ S)
    Psi = np.hstack([S, Y - B0 @ S])
    p = S.shape[1]
    M = np.block([[W @ (S.T @ B0 @ S - X) @ W, W], [W, np.zeros((p, p))]])
    return B0 + Psi @ M @ Psi.T


def mss_eig(S, Y, zeta, zc=None, rtol=1e-10):
    """Partial eigendecomposition of the MSS matrix with the (dense) initial matrix
    B0 = zeta P_par P_par^T + zc P_perp P_perp^T  ([ER] (17)-(18), [BEM] (14)-(15)):
        B = P_par diag(lam) P_par^T + zc (I - P_par P_par^T).
    Psi = [S, Y], M = [[-zeta W - W X W, W], [W, 0]]  ([BMP] (26), [BEM] (15)); pivoted thin QR Psi Pi = Q R,
    R M R^T = U Lam_hat U^T, P_par = Q U, lam = Lam_hat + zeta  ([ER] Sec. 3.1, (16), (25)).
    Returns (P_par (n x r), lam (r,), zc)."""
    if zc is None:
        zc = zeta
    nrm = np.linalg.norm(S, axis=0)
    Sn, Yn = S / nrm, Y / nrm  # pair normalization (B is invariant)
    MY = Sn.T @ Yn
    X = np.tril(MY) + np.tril(MY, -1).T  # newer-s/older-y triangle
    # Obtain (S.T S)^-1 from a QR factor, avoiding Cholesky of the
    # squared-condition Gram matrix for nearly dependent stored steps.
    rs = sla.qr(Sn, mode="r")[0][: Sn.shape[1], :]
    ri = sla.solve_triangular(rs, np.eye(rs.shape[0]))
    W = ri @ ri.T
    WXW = W @ X @ W
    p = S.shape[1]
    M = np.block([[-zeta * W - WXW, W], [W, np.zeros((p, p))]])
    M = 0.5 * (M + M.T)
    Psi = np.hstack([Sn, Yn])
    Q, R, piv = sla.qr(Psi, mode="economic", pivoting=True)
    rd = np.abs(np.diag(R))
    r = int(np.sum(rd > rtol * rd[0])) if rd.size and rd[0] > 0 else 0
    Rr = R[:r, :]
    Mp = M[np.ix_(piv, piv)]
    K = Rr @ Mp @ Rr.T
    lamh, U = np.linalg.eigh(0.5 * (K + K.T))
    return Q[:, :r] @ U, lamh + zeta, zc


def mss_dense_from_eig(P, lam, zc):
    n = P.shape[0]
    return P @ (lam[:, None] * P.T) + zc * (np.eye(n) - P @ P.T)


# ----------------------------------------------------------------------------- pair selection
def select_pairs(Sl, sigma, m):
    """Indices (increasing = oldest first) of the pairs kept: the newest always, older ones newest-first if
    sigma-regular w.r.t. those already kept ([BMP] (27), Algorithm 5.1), at most m."""
    idx, Q = [], None
    for i in range(len(Sl) - 1, -1, -1):
        s = Sl[i]
        ns = np.linalg.norm(s)
        if not (ns > 0) or not np.isfinite(ns):
            continue
        r = s.copy()
        if Q is not None:
            for _ in range(2):  # Gram-Schmidt with reorthogonalization
                r = r - Q @ (Q.T @ r)
        nr = np.linalg.norm(r)
        if nr >= sigma * ns:
            q = (r / nr)[:, None]
            Q = q if Q is None else np.hstack([Q, q])
            idx.append(i)
            if len(idx) >= m:
                break
    return sorted(idx)


# ----------------------------------------------------------------------------- l2 TR subproblem (OBS)
def tr_subproblem(g, P, lam, zc, delta):
    """Exact l2 subproblem via OBS in t = sigma + lambda_min (no near-hard cancellation)."""
    from xrbench.methods._trust_region import obs_subproblem

    return obs_subproblem(g, P, lam, zc, delta)


# ----------------------------------------------------------------------------- More-Thuente search
def mt_search(O, x, f0, g0, d, a0, c1=1e-4, c2=0.9, maxls=20, xtol=1e-14, stpmax=1e20, allow_armijo_fallback=False):
    """Strong Wolfe search (MINPACK dcsrch, More-Thuente, through scipy).  Each trial is one O.fg call.
    Returns (alpha, x_new, f_new, g_new) or None. Default requires strong Wolfe;
    the source SC initial search retains a finite sufficient-decrease seed on warning."""
    dg0 = float(g0 @ d)
    cache = {}
    best = [None]
    big = abs(f0) + 1e10 * (1.0 + abs(f0))

    def ev(a):
        if a not in cache:
            xa = x + a * d
            if not np.isfinite(a) or a < 0 or not np.all(np.isfinite(xa)):
                cache[a] = (big, abs(dg0) * 1e10, xa, None)
                return cache[a]
            fa, ga = O.fg(xa)
            if np.isfinite(fa) and np.all(np.isfinite(ga)):
                dga = float(ga @ d)
                cache[a] = (fa, dga, xa, ga)
                if (
                    a > 0
                    and not np.array_equal(xa, x)
                    and fa <= f0 + c1 * a * dg0
                    and (best[0] is None or fa < best[0][1])
                ):
                    best[0] = (a, fa)
            else:
                cache[a] = (big, abs(dg0) * 1e10, xa, None)  # push the search back towards 0
        return cache[a]

    ls = DCSRCH(lambda a: ev(a)[0], lambda a: ev(a)[1], c1, c2, xtol, 0.0, stpmax)
    try:
        stp, _, _, task = ls(a0, phi0=f0, derphi0=dg0, maxiter=maxls)
    except (ValueError, FloatingPointError, ZeroDivisionError):
        stp = None
    if (
        stp is not None
        and np.isfinite(stp)
        and stp > 0
        and stp in cache
        and cache[stp][3] is not None
        and not np.array_equal(cache[stp][2], x)
    ):
        fa, dga, xa, ga = cache[stp]
        if dg0 < 0 and fa <= f0 + c1 * stp * dg0 and abs(dga) <= -c2 * dg0:
            return stp, xa, fa, ga
    if allow_armijo_fallback and best[0] is not None:
        alpha, _ = best[0]
        fa, _, xa, ga = cache[alpha]
        return alpha, xa, fa, ga
    return None


def _armijo(O, x, f0, g0, d, a0, c1=1e-4, maxbt=60):
    """Armijo backtracking by halving (TR mode, first step)."""
    dg0 = float(g0 @ d)
    a = a0
    for _ in range(maxbt):
        xa = x + a * d
        fa, ga = O.fg(xa)
        if np.isfinite(fa) and np.all(np.isfinite(ga)) and fa <= f0 + c1 * a * dg0:
            return a, xa, fa, ga
        a *= 0.5
    return None


# ----------------------------------------------------------------------------- solver
def solve(
    O,
    x0,
    m=10,
    mode="ls",
    init=None,
    sigma_reg=0.01,
    m2=None,
    c1=1e-4,
    c2=0.9,
    maxls=20,
    pd="pd",
    fallback="sd",
    delta0=1.0,
    eta1=0.01,
    eta2=0.75,
    gam1=0.5,
    gam2=2.0,
    gamp=0.8,
    zeta_lo=1e-4,
    zeta_hi=1e4,
    max_n=None,
    tr_norm="l2",
    q=5,
):
    """L-MSS(m).  mode='ls' (More-Thuente) or 'tr' ([ER] Algorithms 1-2).  m='n' gives full memory.
    init: 'scalar' (gamma = newest y^T y / s^T y; LS default) or 'dense' ([ER] Table 1 Option 4; TR default)."""
    if tr_norm == "linf":
        if mode != "tr":
            raise ValueError("Shape-changing MSS requires mode='tr'")
        return _solve_shape(O, x0, m=m, q=q, init=init or "dense")
    if tr_norm != "l2":
        raise ValueError("tr_norm must be 'l2' or 'linf'")
    x = np.array(x0, dtype=float)
    n = x.size
    if max_n is not None and n > max_n:
        raise ValueError(f"L-MSS: n={n} > max_n={max_n}")
    m = n if m == "n" else int(m)
    if init is None:
        init = "scalar" if mode == "ls" else "dense"
    if m2 is None:
        m2 = int(math.ceil(1.5 * m)) if mode == "ls" else m
    Sl, Yl = [], []
    zeta, zc = 1.0, 1.0  # [ER] zeta_0 = zeta_0^C = 1

    def add_pair(s, y):
        # [ER] (27): accept the pair only if s^T y > eps ||s|| ||y||
        sy = float(s @ y)
        if np.all(np.isfinite(y)) and sy > _EPS * np.linalg.norm(s) * np.linalg.norm(y):
            Sl.append(s.copy())
            Yl.append(y.copy())
            while len(Sl) > m2:  # [ER] Alg. 1: drop the oldest pair
                Sl.pop(0)
                Yl.pop(0)

    def model():
        """Selected pairs and the eigen form of B; updates zeta, zc."""
        nonlocal zeta, zc
        idx = select_pairs(Sl, sigma_reg, m)  # [BMP] (27), Alg. 5.1
        if not idx:
            return None
        S = np.column_stack([Sl[i] for i in idx])
        Y = np.column_stack([Yl[i] for i in idx])
        sn, yn = Sl[-1], Yl[-1]
        bb = float(yn @ yn) / float(sn @ yn)  # newest y^T y / y^T s ([ER] Table 1)
        if init == "scalar":  # Option 1: zeta = zeta^C
            if np.isfinite(bb) and bb > 0:
                zeta = zc = bb
        else:  # Option 4 (dense)
            cand = [
                float(Y[:, j] @ Y[:, j]) / float(S[:, j] @ Y[:, j])
                for j in range(S.shape[1])
                if S[:, j] @ Y[:, j] > 0
            ]
            zn = max(cand) if cand else zeta
            if zeta_lo <= zn <= zeta_hi:  # [ER] Sec. 5: else keep the previous value
                zeta = zn
            if np.isfinite(bb) and zeta_lo <= bb <= zeta_hi:
                zc = bb
        try:
            return mss_eig(S, Y, zeta, zc)
        except (np.linalg.LinAlgError, ValueError):
            return None

    f, g = O.fg(x)

    # ========================================================================= line-search mode
    if mode == "ls":
        fails = 0
        while True:
            em = model()
            a0 = 1.0
            d = None
            if em is not None:
                P, lam, zcur = em
                a = P.T @ g
                gp = g - P @ a
                lmax = max(float(np.max(np.abs(lam))), zcur)
                if pd in ("step", "pd"):
                    ok = (
                        lam.min() > 1e-12 * lmax
                        if pd == "pd"
                        else np.all(np.abs(lam) > 1e-14 * lmax)
                    )
                    if ok:
                        d = -(
                            P @ (a / lam) + (gp / zcur if P.shape[1] < n else 0.0)
                        )  # d = -B^{-1} g
                        # B positive on the step: d^T B d = -g^T d > 0 (with an angle margin)
                        if not (
                            np.all(np.isfinite(d))
                            and g @ d < -1e-10 * np.linalg.norm(g) * np.linalg.norm(d)
                        ):
                            d = None
                if d is None and fallback == "abs":  # modified eigenvalues |lambda|
                    lm = np.maximum(np.abs(lam), 1e-8 * lmax)
                    d = -(P @ (a / lm) + (gp / zcur if P.shape[1] < n else 0.0))
                if d is None:  # steepest-descent fallback (BENCH_PLAN B8)
                    d = -g / zcur
            else:
                d = -g / zc
                if not Sl:
                    a0 = 1.0 / max(
                        np.max(np.abs(d)), 1e-300
                    )  # first step 1/||g0||_inf (harness convention)
            res = mt_search(O, x, f, g, d, a0, c1, c2, maxls)
            if res is None:
                fails += 1
                if fails >= 2:
                    O.note("stop", "line_search_failed")
                    return x
                Sl.clear()
                Yl.clear()  # restart from steepest descent
                continue
            fails = 0
            _, xn, fn, gn = res
            add_pair(xn - x, gn - g)
            x, f, g = xn, fn, gn
            O.mark_iter()

    # ========================================================================= trust-region mode ([ER] Alg. 1-2)
    delta = float(delta0)
    gn0 = float(np.linalg.norm(g))
    d = -g  # B0 = I: steepest descent, Armijo backtracking
    res = _armijo(O, x, f, g, d, min(1.0, delta / max(gn0, 1e-300)), c1)
    if res is None:
        O.note("stop", "initial_line_search_failed")
        return x
    _, xn, fn, gn = res
    s = xn - x
    pred = float(g @ s) + 0.5 * float(s @ s)  # model with B = I
    rho = (fn - f) / pred if pred < 0 else -np.inf
    add_pair(s, gn - g)
    if rho >= eta2 and np.linalg.norm(s) > gamp * delta:  # Algorithm 2
        delta *= gam2
    elif rho < eta1:
        delta *= gam1
    x, f, g = xn, fn, gn
    O.mark_iter()
    while True:
        em = model()
        if em is None:  # no usable pair: B = zc I
            P, lam, zcur = np.zeros((n, 0)), np.zeros(0), zc
        else:
            P, lam, zcur = em
        p, _, pBp = tr_subproblem(g, P, lam, zcur, delta)  # [ER] Thm 1 (12), OBS
        pred = float(g @ p) + 0.5 * pBp
        xt = x + p
        ft, gt = O.fg(xt)
        ok = np.isfinite(ft) and np.all(np.isfinite(gt))
        rho = (ft - f) / pred if (ok and pred < 0) else -np.inf
        if ok:
            add_pair(p, gt - g)  # [ER] Alg. 1: stored whether accepted or not
        if rho >= eta1:  # [ER] Algorithm 2
            if rho >= eta2 and np.linalg.norm(p) > gamp * delta:
                delta *= gam2
            x, f, g = xt, ft, gt
            O.mark_iter()
        else:
            delta *= gam1
        if delta < 100 * _EPS * max(1.0, float(np.linalg.norm(x))):
            O.note("stop", "trust_region_radius_collapsed")
            O.note("radius", delta)
            return x


def _solve_shape(O, x0, m=3, q=5, init="dense", rank_tol=1e-10):
    """SC-INF-D MSS, Brust--Erway--Marcia (2024), Sections 3--4.

    Model memory m and q previous initialization observations are distinct.
    The current observation participates in the maximum before insertion.
    Independent columns are selected from the raw window without imposing
    positive curvature. The complement starts at one and then follows the
    latest positive yy/sy, author whichDenseInit=4. Source details and
    finite-precision differences are in docs/NativeSCAudit.md.
    """
    from collections import deque

    from xrbench.methods._trust_region import shape_infinity_subproblem

    x = np.array(x0, dtype=float)
    n, m, q = x.size, int(m), int(q)
    if m < 1 or q < 1 or init not in {"dense", "scalar"}:
        raise ValueError("Positive memories and dense/scalar initialization required")
    Sl, Yl = [], []
    # Author Init.2 includes the current observation and q previous values.
    curvatures = deque([1.0], maxlen=q)
    zeta = zc = 1.0
    rejected = skipped = 0
    first = True

    def remember(s, y):
        nonlocal skipped, zeta, zc, first
        if not (np.all(np.isfinite(s)) and np.all(np.isfinite(y))):
            return
        sy = float(s @ y)
        bb = float(y @ y) / sy if sy != 0 else None
        if bb is not None and not np.isfinite(bb):
            bb = None
        usable = [v for v in curvatures if v is not None]
        if bb is not None:
            usable.append(bb)
        if usable:
            zeta = max(usable)
        # Author whichDenseInit=4 starts with complement curvature one;
        # later it takes the latest positive physical yy/sy.
        if not first and sy > 0 and bb is not None:
            zc = bb
        curvatures.append(zeta if first else bb)
        first = False
        if np.linalg.norm(s) == 0:
            skipped += 1
            return
        Sl.append(s.copy())
        Yl.append(y.copy())
        if len(Sl) > m:
            Sl.pop(0)
            Yl.pop(0)

    def model():
        zcur = zeta if init == "scalar" else zc
        if not Sl:
            return np.zeros((n, 0)), np.zeros(0), zcur
        S = np.column_stack(Sl)
        lengths = np.linalg.norm(S, axis=0)
        _, R, piv = sla.qr(S / lengths, mode="economic", pivoting=True)
        diagonal = np.abs(np.diag(R))
        rank = int(np.sum(diagonal > rank_tol * diagonal[0]))
        keep = sorted(piv[:rank])
        if not keep:
            return np.zeros((n, 0)), np.zeros(0), zcur
        return mss_eig(S[:, keep], np.column_stack(Yl)[:, keep], zeta, zcur)

    f, g = O.fg(x)
    gn = float(np.linalg.norm(g))
    if not (np.isfinite(gn) and gn > 0):
        O.note("stop", "zero_or_nonfinite_gradient")
        return x
    result = mt_search(O, x, f, g, -g, 1.0, maxls=3000, xtol=1e-6, stpmax=5.0, allow_armijo_fallback=True)
    if result is None:
        O.note("stop", "initial_line_search_failed")
        return x
    _, xn, fn, gn_vec = result
    s = xn - x
    remember(s, gn_vec - g)
    delta = 2.0 * float(np.linalg.norm(s))  # SC-SR1 Algorithm 5, line 34
    x, f, g = xn, fn, gn_vec
    O.mark_iter()
    try:
        while True:
            try:
                P, lam, zcur = model()
                p, pBp = shape_infinity_subproblem(g, P, lam, zcur, delta)
            except (np.linalg.LinAlgError, ValueError) as ex:
                O.note("stop", "numerical_model_failure")
                O.note("detail", str(ex))
                return x
            pred = -(float(g @ p) + 0.5 * pBp)
            xt = x + p
            if np.array_equal(xt, x):
                O.note("stop", "unrepresentable_step")
                return x
            ft, gt = O.fg(xt)
            finite = np.isfinite(ft) and np.all(np.isfinite(gt))
            ratio = (f - ft) / pred if finite and pred > 0 else -np.inf
            if finite:
                remember(p, gt - g)
            # SC-SR1 Algorithm 5, c1=9e-4, c2=c6=.75, c3=.8,
            # c4=2, c5=.1, c7=.5. The radius test uses the Euclidean norm.
            if ratio > 9e-4:
                x, f, g = xt, ft, gt
                O.mark_iter()
            else:
                rejected += 1
            if ratio > 0.75:
                if np.linalg.norm(p) > 0.8 * delta:
                    delta *= 2.0
            elif ratio < 0.1:
                delta *= 0.5
            if delta < 100 * _EPS * max(1.0, float(np.linalg.norm(x))):
                O.note("stop", "trust_region_radius_collapsed")
                return x
    finally:
        O.note("counters", {"nrej": rejected, "nskip": skipped})
