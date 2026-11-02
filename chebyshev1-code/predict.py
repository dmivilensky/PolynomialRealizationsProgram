"""Predictions of Corollary 8.1, computed before any simulation from one
eigendecomposition of the reference Hessian (G_s(H) and r_s(H) are diagonal in its
eigenbasis)."""
import numpy as np
from common import coefficients, tails, residuals


# ---------------------------------------------------------------- gossip, isotropic e_0
def gossip_iso(B, w, eig, N, mu, L, method):
    """For e_0 uniform on the unit sphere of the complement of constants:
    det   = E||p_N(L) e_0||^2                      (error without failures),
    Gamma = leading coefficient of the excess,      E||e_N - p_N(L)e_0||^2 = p/(1-p) Gamma + O(p^2)
    (Corollary 8.1(b)); since E e_N = p_N(L) e_0, the mean squared error is det + excess."""
    coef = coefficients(method, N, mu, L)
    G2 = tails(coef, eig.lam) ** 2
    R2 = residuals(coef, eig.lam) ** 2
    ga = coef[2]
    BU2 = (B @ eig.U) ** 2
    per_k = np.zeros(len(eig.lam))
    for s in range(N):
        per_k += ga[s] ** 2 * R2[s] * (BU2.T @ (w ** 2 * (BU2 @ G2[s])))
    return float(R2[N][1:].mean()), float(per_k[1:].mean())     # drop the constant vector


# ---------------------------------------------------------------- smooth energy
def Z_energy(eig, N, mu, L, ustar, v, method):
    """Second-order term Z(v) of Corollary 8.1(a): e_N - p_N(H*) e_0 = Z(e_0) + O(|e_0|^3)
    for grad f(u* + e) = H* e + 3 u* e^2 + e^3 (componentwise)."""
    coef = coefficients(method, N, mu, L)
    ga = coef[2]
    G = tails(coef, eig.lam)
    R = residuals(coef, eig.lam)
    c0 = eig.U.T @ v
    Z = np.zeros_like(v)
    for s in range(N):
        es = eig.U @ (R[s] * c0)
        Z -= ga[s] * eig.apply(G[s], 3 * ustar * es ** 2)
    return Z


def linear_energy(eig, N, mu, L, v, method):
    """p_N(H*) v, the same vector for every final-Chebyshev-exact method."""
    coef = coefficients(method, N, mu, L)
    return eig.apply(residuals(coef, eig.lam)[N], v)
