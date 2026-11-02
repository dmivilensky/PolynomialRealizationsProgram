"""Two-term realizations of the Chebyshev polynomial and their tail functions.

All methods are written as
    x_{s+1} = alpha_s x_s - beta_s x_{s-1} - gamma_s * gradient,   alpha_s - beta_s = 1,
which covers the semi-iterative (prefix-exact) method, the sine--Jacobi method,
the Jacobi method with weights proportional to sin^{1/2}(theta_j) ('quarter', the point
t = 1/4 of the path w_j ~ sin^{2t}(theta_j) of Section 6), and gradient descent with
Chebyshev stepsizes (beta_s = 0).
"""
import numpy as np

METHODS = ('pref', 'sine', 'quarter', 'gd')   # gd = Chebyshev stepsizes, fractal order


def chebyshev_roots(N, mu, L):
    """Roots lambda_j = (Delta/2)(eta - zeta_j) of p_N^*, increasing in j."""
    j = np.arange(1, N + 1)
    zeta = np.cos((2 * j - 1) * np.pi / (2 * N))
    eta = (L + mu) / (L - mu)
    return (L - mu) / 2 * (eta - zeta)


def fractal_order(N):
    """Fractal (Lebedev--Finogenov) permutation of 0..N-1, N a power of two
    (Agarwal, Goel and Zhang 2021, Definition 5)."""
    if N & (N - 1):
        raise ValueError('fractal order needs N = 2^k')
    s = [1]
    while len(s) < N:
        n = len(s)
        s = [v for a in s for v in (a, 2 * n + 1 - a)]
    return np.array(s) - 1


def sine_couplings(N):
    """a_s^2, s = 1..N-1, of the sine--Jacobi matrix (Theorem 6.1)."""
    s = np.arange(1, N)
    h = np.pi / N
    return np.sin(s * h) ** 2 / (4 * np.sin((s - .5) * h) * np.sin((s + .5) * h))


def path_jacobi(N, t):
    """Diagonal b_s and couplings a_s^2 of the Jacobi matrix whose spectral measure
    (of the first basis vector) has weights w_j ~ sin^{2t}(theta_j) on the Chebyshev
    nodes; Lanczos with full reorthogonalization.  t = 0: semi-iterative, t = 1/2: sine,
    t = 1: reversed semi-iterative."""
    th = (2 * np.arange(1, N + 1) - 1) * np.pi / (2 * N)
    z, w = np.cos(th), np.sin(th) ** (2 * t)
    w = w / w.sum()
    Q = np.zeros((N, N)); Q[:, 0] = np.sqrt(w)
    b, a2 = np.zeros(N), np.zeros(N)
    for k in range(N):
        v = z * Q[:, k]
        b[k] = Q[:, k] @ v
        for _ in range(2):
            v -= Q[:, :k + 1] @ (Q[:, :k + 1].T @ v)
        if k < N - 1:
            a2[k + 1] = v @ v
            Q[:, k + 1] = v / np.sqrt(a2[k + 1])
    return b, a2


def coefficients(method, N, mu, L):
    """(alpha, beta, gamma) arrays of length N."""
    D = L - mu
    eta = (L + mu) / D
    al, be, ga = np.ones(N), np.zeros(N), np.zeros(N)
    if method == 'gd':
        ga[:] = 1.0 / chebyshev_roots(N, mu, L)[fractal_order(N)]
        return al, be, ga
    a2, b = np.zeros(N), np.zeros(N)
    if method == 'pref':
        a2[1:] = 0.25
        if N > 1:
            a2[1] = 0.5
    elif method == 'sine':
        a2[1:] = sine_couplings(N)
    elif method == 'quarter':
        b, a2 = path_jacobi(N, 0.25)
    else:
        raise ValueError(method)
    p = np.empty(N + 1)                          # p_s = P_s(eta) > 0  (Theorem 5.1)
    p[0], p[1] = 1.0, eta - b[0]
    for s in range(1, N):
        p[s + 1] = (eta - b[s]) * p[s] - a2[s] * p[s - 1]
    al = (eta - b) * p[:N] / p[1:]
    be = a2 * np.r_[0.0, p[:N - 1]] / p[1:]
    ga = 2 * p[:N] / (D * p[1:])
    return al, be, ga


def residuals(coef, lam):
    """r_s(lam) for s = 0..N (rows) at the points lam (columns)."""
    al, be, ga = coef
    N = len(al)
    lam = np.asarray(lam, float)
    r = np.empty((N + 1, lam.size))
    r[0] = 1.0
    prev = np.zeros(lam.size)
    for s in range(N):
        r[s + 1] = (al[s] - ga[s] * lam) * r[s] - be[s] * prev
        prev = r[s]
    return r


def tails(coef, lam):
    """G[s](lam) = G_{N,s+1}(lam): terminal value of the homogeneous recurrence
    started from u_s = 0, u_{s+1} = 1 (Lemma A.1).  Computed backwards in O(N)
    per point: G_{N,s+1} satisfies the adjoint recurrence in s."""
    al, be, ga = coef
    N = len(al)
    lam = np.asarray(lam, float)
    # State (u_t, u_{t-1}) -> (u_{t+1}, u_t) with M_t = [[a_t - g_t lam, -b_t], [1, 0]],
    # so G_{N,s+1} = e_1^T M_{N-1} ... M_{s+1} (1, 0)^T.
    G = np.empty((N, lam.size))
    # Backward: w_t^T = w_{t+1}^T M_t, with w_N = (1, 0); then G_{N,s+1} = w_{s+1}^T (1, 0)^T.
    w0, w1 = np.ones(lam.size), np.zeros(lam.size)
    G[N - 1] = w0
    for t in range(N - 1, 0, -1):
        m00 = al[t] - ga[t] * lam
        w0, w1 = w0 * m00 + w1, -w0 * be[t]
        G[t - 1] = w0
    return G


class Eig:
    """Eigendecomposition of a symmetric reference Hessian."""

    def __init__(self, H):
        self.H = H
        self.lam, self.U = np.linalg.eigh(H)

    def apply(self, f, v):
        """f(H) v for a vector of values f on the spectrum."""
        return self.U @ (f * (self.U.T @ v))

    def unperturbed(self, coef, e0):
        """e_s^0 = r_s(H) e0, s = 0..N (rows)."""
        r = residuals(coef, self.lam)
        return (r * (self.U.T @ e0)) @ self.U.T


def chebyshev_eps(N, mu, L):
    eta = (L + mu) / (L - mu)
    return 1.0 / np.cosh(N * np.arccosh(eta))
