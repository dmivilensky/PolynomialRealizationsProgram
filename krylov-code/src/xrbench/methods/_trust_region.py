"""Shared OBS solver in the shifted secular variable; see BEM (2017), Algorithm 1."""

import numpy as np


def shape_norm(p, P):
    """The (P, infinity) norm: max(||P.T p||_inf, ||(I-PP.T)p||_2)."""
    a = P.T @ p
    perp = p - P @ a
    return max(float(np.max(np.abs(a))) if a.size else 0.0, float(np.linalg.norm(perp)))


def shape_infinity_subproblem(g, P, lam, gamma, delta):
    """Closed-form (P, infinity) trust-region solution, Brust--Erway--Marcia
    (2024), equations (19)--(22), and SC-SR1 (2022), Algorithm 3.

    The parallel coordinates solve independent scalar box quadratics; the
    orthogonal complement solves an isotropic Euclidean ball problem. No dense
    complement basis or Hessian is formed. Negative complement curvature and
    the zero-gradient hard case are included. Returns (p, p.T B p).
    """
    if not (np.isfinite(delta) and delta > 0):
        raise ValueError("The trust-region radius must be finite and positive")
    g = np.asarray(g, dtype=float)
    lam = np.asarray(lam, dtype=float)
    a = P.T @ g
    # Choose the positive endpoint when the linear term is zero and curvature
    # negative. Either endpoint is an exact minimizer of that scalar problem.
    v = -delta * np.where(a < 0, -1.0, 1.0)
    flat = (lam == 0.0) & (a == 0.0)
    v[flat] = 0.0
    positive = lam > 0
    v[positive] = np.clip(-a[positive] / lam[positive], -delta, delta)
    gp = g - P @ a if P.shape[1] < g.size else np.zeros_like(g)
    ngp = float(np.linalg.norm(gp))
    if gamma > 0 and ngp <= delta * gamma:
        pp = -gp / gamma
    elif ngp > 0:
        pp = -(delta / ngp) * gp
    elif gamma < 0 and P.shape[1] < g.size:
        # Find a complement vector without constructing an n-by-n basis.
        # The coordinate with least projection has complement norm bounded
        # away from zero whenever the complement is nonempty.
        row = int(np.argmin(np.einsum("ij,ij->i", P, P)))
        pp = -(P @ P[row, :])
        pp[row] += 1.0
        pp *= delta / np.linalg.norm(pp)
    else:
        pp = np.zeros_like(g)
    p = P @ v + pp
    pBp = float(np.dot(lam, v * v) + gamma * np.dot(pp, pp))
    return p, pBp


def obs_subproblem(g, P, lam, gamma, delta, maxit=100):
    """Global minimizer of g^T p + p^T B p / 2 s.t. ||p|| <= delta, B = P diag(lam) P^T + gamma (I - P P^T), gamma > 0
    ([BEM] Algorithm 1).  Optimality: (B + sigma I) p = -g, B + sigma I psd, sigma (delta - ||p||) = 0, sigma >= 0.
    In the eigenbasis p(sigma) = -P (lam + sigma)^{-1} P^T g - g_perp / (gamma + sigma).
      * lambda_min > 0 and ||p(0)|| <= delta: sigma* = 0 (Algorithm 1, first branch);
      * lambda_min <= 0, g without component on the lambda_min eigenspace and ||p(-lambda_min)|| <= delta: hard case,
        sigma* = -lambda_min, p* = -(B + sigma* I)^+ g + alpha u_min with ||p*|| = delta ((13)-(14), Thm 2);
      * otherwise Newton on phi(sigma) = 1/||p(sigma)|| - 1/delta (8) in (max(-lambda_min, 0), inf), started to the
        left of the root (phi concave increasing: monotone convergence; [BEM] Thm 3 gives another left start).
    Implementation: sigma = t - lambda_min with t >= max(lambda_min, 0) as the Newton variable and the shifted
    eigenvalues lam - lambda_min, gamma - lambda_min formed once, so that lam_i + sigma = (lam_i - lambda_min) + t is
    exact for the lambda_min components. Both MSS/TR and L-SR1/TR share this solver;
    no matrix, radius policy or mathematical subproblem is changed.
    Returns (p, sigma, p^T B p)."""
    n, r = P.shape
    a = P.T @ g
    has_perp = r < n
    gp = (g - P @ a) if has_perp else np.zeros(n)
    gp2 = float(gp @ gp)
    lmin = min(float(lam.min()) if r else np.inf, gamma if has_perp else np.inf)
    dl = lam - lmin  # shifted eigenvalues (>= 0)
    dg = gamma - lmin
    gnorm = float(np.linalg.norm(g))
    on_min = dl <= 1e-12 * max(1.0, abs(lmin))
    if has_perp and dg <= 1e-12 * max(1.0, abs(lmin)):
        dg = 0.0
    amin2 = float(np.sum(a[on_min] ** 2)) + (gp2 if dg == 0.0 else 0.0)
    negl = amin2 <= (1e-14 * gnorm) ** 2  # no (numerical) component on u_min
    keep = ~on_min if negl else np.ones(r, dtype=bool)
    dl_k = np.where(on_min & ~keep, 1.0, dl)  # excluded components: placeholder (a set to 0)
    a_k = np.where(keep, a, 0.0)
    use_perp = has_perp and not (negl and dg == 0.0)

    def nrm2(t):
        v = float(np.sum((a_k / (dl_k + t)) ** 2)) if r else 0.0
        return v + (gp2 / (dg + t) ** 2 if use_perp else 0.0)

    def finish(t):
        vpar = -a_k / (dl_k + t) if r else np.zeros(0)
        p = P @ vpar + ((-gp / (dg + t)) if use_perp else 0.0)
        pBp = float(np.sum(lam * vpar**2)) + (gamma * gp2 / (dg + t) ** 2 if use_perp else 0.0)
        return p, vpar, pBp

    t_lo = max(lmin, 0.0)  # sigma >= 0 and lam + sigma >= 0
    if lmin > 0 and nrm2(lmin) <= delta**2:  # interior: sigma* = 0
        p, _, pBp = finish(lmin)
        return p, 0.0, pBp
    if lmin <= 0 and negl and nrm2(0.0) <= delta**2:  # hard case (13)-(14)
        p, vpar, pBp = finish(0.0)
        alpha = float(np.sqrt(max(delta**2 - float(p @ p), 0.0)))
        u = P[:, int(np.flatnonzero(on_min)[0])]  # lambda_min <= 0 < gamma: u_min lies in range(P)
        return p + alpha * u, -lmin, pBp + lmin * alpha**2
    # Newton on phi(t) = 1/||p|| - 1/delta from the left of the root
    t = t_lo
    if not negl and lmin <= 0:
        t = max(t_lo, np.sqrt(amin2) / delta)  # ||p(t)|| >= |a_min| / t  =>  t* >= |a_min| / delta
    if t <= 0.0:
        t = np.nextafter(0.0, 1.0)
    for _ in range(maxit):
        nn = np.sqrt(nrm2(t))
        if not np.isfinite(nn) or nn == 0.0 or abs(nn - delta) <= 1e-13 * delta:
            break
        dn = (float(np.sum(a_k**2 / (dl_k + t) ** 3)) if r else 0.0) + (
            gp2 / (dg + t) ** 3 if use_perp else 0.0
        )
        if not dn > 0:
            break
        tn = t - (1.0 / nn - 1.0 / delta) * nn**3 / dn  # Newton step on (8)
        if not np.isfinite(tn) or tn < t_lo:
            tn = t_lo if t_lo > 0 else 0.5 * t
        if abs(tn - t) <= 1e-15 * t:
            t = tn
            break
        t = tn
    p, _, pBp = finish(t)
    return p, max(t - lmin, 0.0), pBp
