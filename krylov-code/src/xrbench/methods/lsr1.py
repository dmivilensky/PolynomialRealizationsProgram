"""Limited-memory SR1 with Euclidean and shape-changing trust regions.

Primary preset: SC-INF, Init. 2, m=5 model pairs and q=7 initialization
observations, from Brust, Burdakov, Erway and Marcia, Algorithm 1030: SC-SR1:
MATLAB Software for Limited-memory SR1 Trust-region Methods, ACM Trans. Math.
Softw. 48(4), Article 48 (2022), https://doi.org/10.1145/3550269,
https://arxiv.org/abs/1607.03533. See Algorithm 3 for the subproblem,
equation (40) for max-history initialization and Algorithm 5 for the outer loop.

[BNS] Byrd, Nocedal and Schnabel, Representations of quasi-Newton matrices and
their use in limited memory methods, Math. Program. 63 (1994), 129--156:
Theorem 5.1 gives the compact matrix used by sr1_eig and sr1_compact.
[NW] Nocedal and Wright, Numerical Optimization, second edition (2006):
Algorithm 6.2 and equation (6.26) give the SR1 update/skip rule, applied to
accepted and rejected trials. The model change is v v.T/(s.T v), v=y-Bs.
[BEM] Brust, Erway and Marcia, On solving L-SR1 trust-region subproblems,
Comput. Optim. Appl. 66 (2017), 245--266,
https://doi.org/10.1007/s10589-016-9868-3: Euclidean OBS subproblem solver.
[EGMO] Erway et al., Trust-region algorithms for training responses, Optim.
Methods Softw. 35 (2020), 460--487: the optional generalized-eigenvalue
initialization in the Euclidean reference path.

The SC reference follows author LSR1_SC Init.2: alpha0=1, More--Thuente
c1=1e-4,c2=.9, xtol=1e-6, stpmax=5,maxfev=3000. Its q previous raw
curvatures and current observation determine gamma. The author's compact
base-vector skip test uses y-gamma*s with updated gamma and the experimental
absolute floor 1e-10. The same coherent test is used on the first pair; the
first author-code test has an inconsistent product instead of division.
Pair normalization occurs only after the physical skip decision. Pivoted QR
with relative rank tolerance 1e-10 replaces the author Gram-LDL basis, and a
relative machine-radius stop is used. See docs/NativeSCAudit.md.

The Euclidean reference path supports yy, sy and egmo initialization. Its
default yy scalar rule and egmo factor .9 are explicit implementation choices;
they are not claimed to reproduce the SC author's default optimizer.
All paths use the shared oracle's stopping/budgets. Numerical rank cleanup and
a relative machine-radius stop are documented in docs/CompetitorAudit.md.
"""

import numpy as np
import scipy.linalg as sla

from xrbench.methods._trust_region import obs_subproblem

_EPS = np.finfo(float).eps


# ----------------------------------------------------------------------------- SR1 algebra
def sym_lower(S, Y):
    """D + L + L^T of [BNS] Thm 5.1 (oldest first: L_ij = s_i^T y_j, i > j)."""
    M = S.T @ Y
    return np.tril(M) + np.tril(M, -1).T


def sr1_compact(S, Y, gamma):
    """Dense SR1 matrix from the compact form [BNS] Thm 5.1 / [BEM] (4), B0 = gamma I (tests, small n)."""
    n = S.shape[0]
    Psi = Y - gamma * S
    K = sym_lower(S, Y) - gamma * (S.T @ S)
    return gamma * np.eye(n) + Psi @ np.linalg.solve(K, Psi.T)


def sr1_dense(S, Y, gamma, r=1e-8):
    """Dense SR1 recursion B+ = B + v v^T / (v^T s), v = y - B s, from B0 = gamma I, with the skipping rule
    [NW] (6.26).  Returns (B, kept indices)."""
    n = S.shape[0]
    B = gamma * np.eye(n)
    kept = []
    for i in range(S.shape[1]):
        s, y = S[:, i], Y[:, i]
        v = y - B @ s
        nv = np.linalg.norm(v)
        if nv > 0 and abs(s @ v) >= r * np.linalg.norm(s) * nv:  # [NW] (6.26)
            B = B + np.outer(v, v) / (v @ s)  # [NW] (6.24)
            kept.append(i)
    return B, kept


def sr1_select(S, Y, gamma, r=1e-8):
    """Indices (oldest first) of the pairs whose SR1 updates pass the skipping test (6.26) in the recursion from
    B0 = gamma I (B_{k} s_k evaluated with the compact form of the pairs kept so far)."""
    p = S.shape[1]
    Psi = Y - gamma * S
    K = sym_lower(S, Y) - gamma * (S.T @ S)
    PsiTS = Psi.T @ S
    kept = []
    for i in range(p):
        s, y = S[:, i], Y[:, i]
        Bs = gamma * s
        if kept:
            try:
                Bs = Bs + Psi[:, kept] @ np.linalg.solve(
                    K[np.ix_(kept, kept)], PsiTS[kept, i]
                )  # [BNS] Thm 5.1
            except np.linalg.LinAlgError:
                continue
        v = y - Bs
        nv = float(np.linalg.norm(v))
        if nv > 0 and np.isfinite(nv) and abs(s @ v) >= r * np.linalg.norm(s) * nv:  # [NW] (6.26)
            kept.append(i)
    return kept


def lambda_hat(S, Y):
    """Smallest eigenvalue of (D + L + L^T) u = lambda S^T S u ([EGMO]); None if S^T S is not positive definite."""
    nrm = np.linalg.norm(S, axis=0)
    Sn, Yn = S / nrm, Y / nrm
    try:
        w = sla.eigh(sym_lower(Sn, Yn), Sn.T @ Sn, eigvals_only=True)
    except (np.linalg.LinAlgError, ValueError):
        return None
    return float(w[0]) if np.all(np.isfinite(w)) else None


def sr1_eig(S, Y, gamma, rtol=1e-10):
    """Partial eigendecomposition [BEM] (7), Algorithm 1 steps 1-3: B = P diag(lam) P^T + gamma (I - P P^T).
    Psi = Y - gamma S = Q R (pivoted, truncated), R M R^T = U Lam_hat U^T, P = Q U, lam = Lam_hat + gamma."""
    nrm = np.linalg.norm(S, axis=0)
    Sn, Yn = S / nrm, Y / nrm  # pair normalization (B is invariant)
    Psi = Yn - gamma * Sn  # [BEM] (4)
    K = sym_lower(Sn, Yn) - gamma * (Sn.T @ Sn)  # M^{-1} of [BEM] (4)
    Q, R, piv = sla.qr(Psi, mode="economic", pivoting=True)
    rd = np.abs(np.diag(R))
    rk = int(np.sum(rd > rtol * rd[0])) if rd.size and rd[0] > 0 else 0
    if rk == 0:
        return np.zeros((S.shape[0], 0)), np.zeros(0)
    Rr = R[:rk, :]
    Kp = K[np.ix_(piv, piv)]
    Z = np.linalg.solve(Kp, Rr.T)  # M R^T (M = K^{-1})
    lamh, U = np.linalg.eigh(0.5 * (Rr @ Z + (Rr @ Z).T))
    return Q[:, :rk] @ U, lamh + gamma


def eig_dense(P, lam, gamma):
    n = P.shape[0]
    return P @ (lam[:, None] * P.T) + gamma * (np.eye(n) - P @ P.T)


def apply_B(P, lam, gamma, v):
    a = P.T @ v
    return P @ (lam * a) + gamma * (v - P @ a)


# ----------------------------------------------------------------------------- l2 subproblem (OBS)


# ----------------------------------------------------------------------------- solver
def solve(O, x0, m=5, gamma="yy", r=1e-8, eta=1e-4, delta0=1.0, gamma_frac=0.9, tr_norm="l2", q=7):
    """L-SR1(m) trust-region method ([NW] Alg. 6.2 / [BKS] in limited memory, [BEM] OBS subproblem)."""
    if tr_norm == "linf":
        if gamma != "max":
            raise ValueError("Published SC-SR1 uses gamma='max' (Init. 2)")
        return _solve_shape(O, x0, m=m, q=q, r=r)
    if tr_norm != "l2":
        raise ValueError("tr_norm must be 'l2' or 'linf'")
    x = np.array(x0, dtype=float)
    n = x.size
    m = int(m)
    Sl, Yl = [], []
    gam = 1.0  # B0 = I at the first iteration
    delta = float(delta0)
    nskip = nrej = 0
    f, g = O.fg(x)
    try:
        while True:
            # ---- model: gamma, pairs passing (6.26) with that gamma, eigen form [BEM] (7)
            P, lam = np.zeros((n, 0)), np.zeros(0)
            if Sl:
                S = np.column_stack(Sl)
                Y = np.column_stack(Yl)
                if gamma not in ("yy", "sy", "egmo"):
                    raise ValueError(gamma)
                for j in range(len(Sl) - 1, -1, -1):  # newest pair with s^T y > 0: NW (6.20)
                    sy = float(Sl[j] @ Yl[j])
                    if sy > 0:
                        gy = (
                            sy / float(Sl[j] @ Sl[j])
                            if gamma == "sy"
                            else float(Yl[j] @ Yl[j]) / sy
                        )
                        if np.isfinite(gy) and gy > 0:
                            gam = gy
                        break
                if gamma == "egmo":  # [EGMO]: gamma strictly below lambda_hat
                    lh = lambda_hat(S, Y)
                    if lh is not None and lh > 0:
                        gam = min(gam, gamma_frac * lh)
                nrm = np.linalg.norm(S, axis=0)
                kept = sr1_select(S / nrm, Y / nrm, gam, r)
                if kept:
                    try:
                        P, lam = sr1_eig(S[:, kept], Y[:, kept], gam)
                    except (np.linalg.LinAlgError, ValueError):
                        P, lam = np.zeros((n, 0)), np.zeros(0)
            # ---- trust-region step ([NW] Alg. 6.2; subproblem [BEM] Alg. 1)
            p, _, pBp = obs_subproblem(g, P, lam, gam, delta)  # [BEM] Algorithm 1
            pred = -(float(g @ p) + 0.5 * pBp)
            xt = x + p
            ft, gt = O.fg(xt)
            ok = bool(np.isfinite(ft) and np.all(np.isfinite(gt)))
            ratio = (f - ft) / pred if (ok and pred > 0) else -np.inf  # ared / pred
            if ok:  # update even if the step is rejected ([BKS], [NW])
                y = gt - g
                v = y - apply_B(P, lam, gam, p)
                nv = float(np.linalg.norm(v))
                if (
                    nv > 0 and abs(p @ v) >= r * np.linalg.norm(p) * nv
                ):  # [NW] (6.26) with the current B
                    Sl.append(p.copy())
                    Yl.append(y)
                    if len(Sl) > m:
                        Sl.pop(0)
                        Yl.pop(0)
                else:
                    nskip += 1
            if ratio > eta:  # [NW] Alg. 6.2: accept
                x, f, g = xt, ft, gt
                O.mark_iter()
            else:
                nrej += 1
            if ratio > 0.75:  # [NW] Alg. 6.2: radius
                if np.linalg.norm(p) > 0.8 * delta:
                    delta *= 2.0
            elif ratio < 0.1:
                delta *= 0.5
            if delta < 100 * _EPS * max(1.0, float(np.linalg.norm(x))):
                O.note("stop", "tr_radius")
                return x
    finally:
        O.note("counters", {"nskip": nskip, "nrej": nrej})


def _solve_shape(O, x0, m=5, q=7, r=1e-8):
    """SC-SR1/SC-INF, Init. 2, Algorithm 5 of Brust et al. (2022).

    Model memory m and curvature history q are independent. The published
    author compact base-vector skip condition uses y-gamma*s with the updated
    initialization and a physical denominator floor. Compact matrices are
    rebuilt with current gamma without reapplying the gate to old pairs.
    Search and initialization histories follow the original source defaults.
    """
    from collections import deque

    from xrbench.methods._trust_region import shape_infinity_subproblem
    from xrbench.methods.lmss import mt_search

    x = np.array(x0, dtype=float)
    n, m, q = x.size, int(m), int(q)
    if m < 1 or q < 1:
        raise ValueError("Model and initialization memories must be positive")
    Sl, Yl = [], []
    history = deque([1.0], maxlen=q)
    gam = 1.0
    nskip = nrej = 0
    first = True

    def curvature(s, y):
        nonlocal gam, first
        sy = float(s @ y)
        value = float(y @ y) / sy if sy != 0 else None
        if value is not None and not np.isfinite(value):
            value = None
        usable = [v for v in history if v is not None]
        if value is not None:
            usable.append(value)
        if usable:
            gam = max(usable)
        history.append(gam if first else value)
        first = False

    def store(s, y):
        nonlocal nskip
        # Author LSR1_SC uses the compact base vector at UPDATED gamma,
        # with a physical (unnormalized) absolute denominator floor.
        v = y - gam * s
        nv = float(np.linalg.norm(v))
        ns = float(np.linalg.norm(s))
        if ns > 0 and nv > 0 and np.isfinite(nv) and abs(float(s @ v)) > r * max(ns * nv, 1e-10):
            Sl.append(s.copy())
            Yl.append(y.copy())
            if len(Sl) > m:
                Sl.pop(0)
                Yl.pop(0)
        else:
            nskip += 1

    f, g = O.fg(x)
    ng = float(np.linalg.norm(g))
    if not (np.isfinite(ng) and ng > 0):
        O.note("stop", "zero_or_nonfinite_gradient")
        return x
    initial = mt_search(O, x, f, g, -g, 1.0, maxls=3000, xtol=1e-6, stpmax=5.0, allow_armijo_fallback=True)
    if initial is None:
        O.note("stop", "initial_line_search_failed")
        return x
    _, xn, fn, gn = initial
    s, y = xn - x, gn - g
    curvature(s, y)
    store(s, y)
    delta = 2.0 * float(np.linalg.norm(s))
    x, f, g = xn, fn, gn
    O.mark_iter()
    try:
        while True:
            P, lam = np.zeros((n, 0)), np.zeros(0)
            if Sl:
                try:
                    P, lam = sr1_eig(np.column_stack(Sl), np.column_stack(Yl), gam)
                except (np.linalg.LinAlgError, ValueError) as ex:
                    O.note("stop", "numerical_model_failure")
                    O.note("detail", str(ex))
                    return x
            p, pBp = shape_infinity_subproblem(g, P, lam, gam, delta)
            pred = -(float(g @ p) + 0.5 * pBp)
            xt = x + p
            if np.array_equal(xt, x):
                O.note("stop", "unrepresentable_step")
                return x
            ft, gt = O.fg(xt)
            finite = np.isfinite(ft) and np.all(np.isfinite(gt))
            ratio = (f - ft) / pred if finite and pred > 0 else -np.inf
            if finite:
                y = gt - g
                curvature(p, y)
                store(p, y)
            if ratio > 9e-4:
                x, f, g = xt, ft, gt
                O.mark_iter()
            else:
                nrej += 1
            if ratio > 0.75:
                if np.linalg.norm(p) > 0.8 * delta:
                    delta *= 2.0
            elif ratio < 0.1:
                delta *= 0.5
            if delta < 100 * _EPS * max(1.0, float(np.linalg.norm(x))):
                O.note("stop", "trust_region_radius_collapsed")
                return x
    finally:
        O.note("counters", {"nskip": nskip, "nrej": nrej})
