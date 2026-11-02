"""Independent quadratic helpers: strictly convex quadratic (n=20, kappa=1e3) and CG reference."""

import numpy as np

from xrbench.oracle import Oracle, run_method  # noqa: F401


class Quad:
    """f = 1/2 x'Ax - b'x, A = Q diag(geomspace(1, kappa, n)) Q'."""

    convex = True
    err_from_f = True

    def __init__(self, n=20, kappa=1e3, seed=0):
        rng = np.random.default_rng(seed)
        Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
        self.A = (Q * np.geomspace(1, kappa, n)) @ Q.T
        self.A = 0.5 * (self.A + self.A.T)
        self.b = rng.normal(size=n)
        self.n = n
        self.x0 = rng.normal(size=n)
        self.xstar = np.linalg.solve(self.A, self.b)
        self.fstar = self.f(self.xstar)
        self.meta = dict(mu=1.0, L=kappa)
        self.name = "QUAD"

    def f(self, x):
        return 0.5 * x @ self.A @ x - self.b @ x

    def grad(self, x):
        return self.A @ x - self.b

    def hvp(self, x, v):
        return self.A @ v

    def err_f(self, fx):
        return fx - self.fstar


def cg_iterates(P, x0, k):
    """Exact CG iterates x_0..x_k: minimizers of f over x0 + K_p(A, g0), computed with an orthonormal Krylov basis
    (Arnoldi with two Gram-Schmidt passes), so the reference does not suffer CG's loss of orthogonality."""
    g0 = P.grad(x0)
    V = np.zeros((len(x0), 0))
    v = g0 / np.linalg.norm(g0)
    out = [x0.copy()]
    for _ in range(k):
        for _ in range(2):
            v = v - V @ (V.T @ v)
        nv = np.linalg.norm(v)
        if nv < 1e-14:
            out.append(out[-1].copy())
            continue
        V = np.column_stack([V, v / nv])
        c = np.linalg.solve(V.T @ P.A @ V, -(V.T @ g0))
        out.append(x0 + V @ c)
        v = P.A @ V[:, -1]
    return out


def run_gtol(solve, P, params=None, rel=1e-8, budget=5000):
    g0 = np.linalg.norm(P.grad(P.x0))
    return run_method(solve, P, P.x0, params or {}, gtol=rel * g0, budget=budget, max_time=60)
