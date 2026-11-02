"""Small self-contained test problems for the baseline tests (GBB, LMSD, AdaGD/AdaBB, C+AG).

Kept independent of the production problem generators."""

import numpy as np

from xrbench.oracle import Oracle, run_method  # noqa: E402,F401


class Quad:
    """f = 1/2 x'Ax with A = Q diag(lam) Q'; minimizer 0."""

    convex = True
    err_from_f = True
    fstar = 0.0

    def __init__(self, lam, seed=0, x0=None, rotate=True):
        lam = np.asarray(lam, dtype=float)
        self.n = lam.size
        rng = np.random.default_rng(seed)
        if rotate:
            Q, _ = np.linalg.qr(rng.standard_normal((self.n, self.n)))
        else:
            Q = np.eye(self.n)
        self.lam = lam
        self.A = (Q * lam) @ Q.T
        self.A = 0.5 * (self.A + self.A.T)
        self.x0 = rng.standard_normal(self.n) if x0 is None else np.asarray(x0, dtype=float)
        self.name = "QUAD%d" % self.n
        self.L = float(lam.max())

    def f(self, x):
        return 0.5 * float(x @ self.A @ x)

    def grad(self, x):
        return self.A @ x

    def fg(self, x):
        g = self.A @ x
        return 0.5 * float(x @ g), g

    def err_f(self, fx):
        return fx


def quad_kappa(n=20, kappa=1e3, seed=0):
    return Quad(np.geomspace(1.0, kappa, n), seed=seed)


class Rosenbrock:
    """Chained Rosenbrock, f = sum 100 (x_{i+1} - x_i^2)^2 + (1 - x_i)^2, x0 = (-1.2, 1, -1.2, 1, ...)."""

    convex = False
    err_from_f = True
    fstar = None

    def __init__(self, n=10):
        self.n = n
        self.name = "ROS%d" % n
        self.x0 = np.array([-1.2 if i % 2 == 0 else 1.0 for i in range(n)])

    def fg(self, x):
        a = x[1:] - x[:-1] ** 2
        b = 1.0 - x[:-1]
        f = float(100.0 * a @ a + b @ b)
        g = np.zeros_like(x)
        g[:-1] = -400.0 * a * x[:-1] - 2.0 * b
        g[1:] += 200.0 * a
        return f, g

    def f(self, x):
        return self.fg(x)[0]

    def grad(self, x):
        return self.fg(x)[1]


class Logistic:
    """l2-regularized logistic regression, f = mean log(1 + exp(-b_i a_i'x)) + lam/2 ||x||^2, x0 = 0."""

    convex = True
    err_from_f = True
    fstar = None

    def __init__(self, n=20, m=200, lam=1e-3, cond=1e2, seed=0):
        rng = np.random.default_rng(seed)
        U, _ = np.linalg.qr(rng.standard_normal((m, n)))
        V, _ = np.linalg.qr(rng.standard_normal((n, n)))
        s = np.geomspace(1.0, cond, n)
        self.Amat = (U * s) @ V.T * np.sqrt(m) / cond
        w = rng.standard_normal(n)
        self.b = np.sign(self.Amat @ w + 0.5 * rng.standard_normal(m))
        self.b[self.b == 0] = 1.0
        self.lam = lam
        self.n, self.m = n, m
        self.x0 = np.zeros(n)
        self.name = "LOGREG%d" % n

    def fg(self, x):
        z = -self.b * (self.Amat @ x)
        f = float(np.mean(np.logaddexp(0.0, z)) + 0.5 * self.lam * x @ x)
        sgm = 0.5 * (1.0 + np.tanh(0.5 * z))  # 1/(1+exp(-z))
        g = self.Amat.T @ (-self.b * sgm) / self.m + self.lam * x
        return f, g

    def f(self, x):
        return self.fg(x)[0]

    def grad(self, x):
        return self.fg(x)[1]


class Recorder:
    """Wraps a problem and records every point at which the gradient is evaluated (for step-size tests)."""

    def __init__(self, prob):
        self.p = prob
        self.n, self.x0, self.name = prob.n, prob.x0, prob.name
        self.err_from_f = True
        self.gpts = []

    def f(self, x):
        return self.p.f(x)

    def grad(self, x):
        self.gpts.append(np.array(x))
        return self.p.grad(x)

    def fg(self, x):
        self.gpts.append(np.array(x))
        return self.p.fg(x)


def run(solve, prob, params=None, rel=1e-8, budget=200000, x0=None):
    """Run to ||g|| <= rel * ||g0||; returns the oracle summary dict."""
    x0 = prob.x0 if x0 is None else x0
    g0 = np.linalg.norm(getattr(prob, "p", prob).fg(x0)[1])  # not recorded by a Recorder
    return run_method(solve, prob, x0, params or {}, budget=budget, gtol=rel * g0, max_time=300.0)
