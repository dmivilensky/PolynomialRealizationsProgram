"""Simulators.  Common random numbers: the same seed gives the same link failures and
the same initial errors for every method."""
import numpy as np
from common import Eig, residuals


def _random_unit(rng, m, d, center=False):
    """m initial errors uniform on the unit sphere (of the complement of constants if center)."""
    e = rng.standard_normal((m, d))
    if center:
        e -= e.mean(1, keepdims=True)
    return e / np.linalg.norm(e, axis=1, keepdims=True)


def _pN(H, coef):
    eig = Eig(H)
    r = residuals(coef, eig.lam)[len(coef[0])]
    return (eig.U * r) @ eig.U.T


def mc_gossip(B, w, Lap, coef, p, M, seed, chunk=2000):
    """Each link fails independently with probability p in every step, surviving weights
    are divided by 1-p; e_0 is uniform on the unit sphere of the complement of constants,
    independently in each run.  Returns per run (||e_N||^2, ||e_N - p_N(L) e_0||^2)."""
    al, be, ga = coef
    P = _pN(Lap, coef)
    rng = np.random.default_rng(seed)
    full, exc = [], []
    for m in [chunk] * (M // chunk) + ([M % chunk] if M % chunk else []):
        ep = _random_unit(rng, m, Lap.shape[0], center=True); e = ep.copy(); target = ep @ P
        for s in range(len(al)):
            alive = (rng.random((m, len(w))) >= p) * (w / (1 - p))
            g = ((e @ B.T) * alive) @ B
            ep, e = e, al[s] * e - be[s] * ep - ga[s] * g
        full.append((e ** 2).sum(1)); exc.append(((e - target) ** 2).sum(1))
    return np.concatenate(full), np.concatenate(exc)


def run_energy(Hs, ustar, coef, e0):
    """Exact run on f with grad f(u* + e) = H* e + 3 u* e^2 + e^3.
    Returns (e_N, e_N - p_N(H*) e_0); non-finite entries signal divergence."""
    al, be, ga = coef
    target = _pN(Hs, coef) @ e0
    ep, e = e0.copy(), e0.copy()
    with np.errstate(over='ignore', invalid='ignore'):
        for s in range(len(al)):
            g = Hs @ e + 3 * ustar * e ** 2 + e ** 3
            ep, e = e, al[s] * e - be[s] * ep - ga[s] * g
    return e, e - target
