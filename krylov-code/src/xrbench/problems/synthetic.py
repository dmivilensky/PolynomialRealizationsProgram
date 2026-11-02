"""Controlled smooth objectives with known minimizer, never estimated f*.

The perturbed quadratic is the existing manuscript family. The exponential
remainder is evaluated by its Taylor series near zero to avoid cancellation;
this changes numerical evaluation, not the objective. No Hessian information
is supplied to practical solvers.
"""

import numpy as np


def exp_remainder(t):
    t = np.asarray(t)
    small = np.abs(t) < 1e-3
    with np.errstate(over="ignore", invalid="ignore"):
        out = np.expm1(t) - t
        z = t[small]
        out[small] = (
            z * z * (0.5 + z * (1 / 6 + z * (1 / 24 + z * (1 / 120 + z * (1 / 720 + z / 5040)))))
        )
    return out


class SmoothQuadratic:
    convex = True
    err_from_f = False
    fstar = 0.0

    def __init__(self, n=100, kappa=1000.0, epsilon=0.0, seed=0, local=False):
        rng = np.random.default_rng(seed)
        Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
        lam = np.geomspace(1.0, kappa, n)
        self.A = (Q * lam) @ Q.T
        U = rng.normal(size=(n, n))
        U /= np.linalg.norm(U, axis=0)
        self.Ac = (Q * np.sqrt(lam)) @ Q.T @ U
        self.epsilon = epsilon
        self.n = n
        x = np.random.default_rng(100 + seed).normal(size=n)
        self.x0 = x / np.sqrt(x @ self.A @ x)
        if local:
            self.x0 *= 0.03
        self.initial_energy = float(np.sqrt(self.x0 @ self.A @ self.x0))
        # Keep only the last actual evaluation. Energy-error diagnostics then
        # reuse its quadratic action instead of silently adding a dense A@x
        # to every measured gradient call. No Hessian action is exposed to a
        # solver, and setup does not seed a free first oracle evaluation.
        self._last_point = None
        self._last_ax = None
        self._last_energy_squared = None
        self.name = f"PQ-n{n}-k{kappa:g}-e{epsilon:g}-s{seed}" + ("-local" if local else "")
        self.meta = dict(
            source="controlled",
            kappa=kappa,
            epsilon=epsilon,
            seed=seed,
            convex_quadratic=epsilon == 0,
            global_L_valid=epsilon == 0,
        )

    def _quadratic_action(self, x):
        x = np.asarray(x, dtype=float)
        key = (x.shape, x.tobytes())
        if key != self._last_point:
            self._last_ax = self.A @ x
            self._last_energy_squared = float(x @ self._last_ax)
            self._last_point = key
        return self._last_ax

    def f(self, x):
        ax = self._quadratic_action(x)
        if self.epsilon == 0:
            return float(0.5 * x @ ax)
        with np.errstate(over="ignore", invalid="ignore"):
            return float(0.5 * x @ ax + self.epsilon * exp_remainder(self.Ac.T @ x).sum())

    def grad(self, x):
        ax = self._quadratic_action(x)
        if self.epsilon == 0:
            return ax.copy()
        with np.errstate(over="ignore", invalid="ignore"):
            return ax + self.epsilon * self.Ac @ np.expm1(self.Ac.T @ x)

    def fg(self, x):
        ax = self._quadratic_action(x)
        if self.epsilon == 0:
            return float(0.5 * x @ ax), ax.copy()
        with np.errstate(over="ignore", invalid="ignore"):
            t = self.Ac.T @ x
            return (
                float(0.5 * x @ ax + self.epsilon * exp_remainder(t).sum()),
                ax + self.epsilon * self.Ac @ np.expm1(t),
            )

    def err(self, x):
        self._quadratic_action(x)
        return float(np.sqrt(max(0.0, self._last_energy_squared)) / self.initial_energy)

    def err_f(self, fx):
        return float(fx)


class LogBarrier:
    """Analytic-centre problem (self-concordant): f(x) = c^T x - sum_i log(b_i - a_i^T x). err = f - f*."""

    def __init__(self, n=100, m=300, cond=1e4, seed=2):
        rng = np.random.default_rng(seed)
        Q, _ = np.linalg.qr(rng.normal(size=(n, n)))
        Araw = rng.normal(size=(m, n)) * np.geomspace(1, np.sqrt(cond), n) @ Q.T
        self.Am = Araw / np.sqrt(np.mean(np.sum(Araw**2, 1)))
        self.b = 1.0 + rng.uniform(size=m)
        self.c = -0.5 * self.Am.T @ (1.0 / self.b)  # moves the centre away from the start x0 = 0
        self.fstar = None
        self.n = n
        self.x0 = np.zeros(n)
        self.name = "AnalyticCentre"
        self.meta = {}

    def slack(self, x):
        return self.b - self.Am @ x

    def f(self, x):
        s = self.slack(x)
        if np.any(s <= 0):
            return np.inf
        return self.c @ x - np.sum(np.log(s))

    def grad(self, x):
        s = self.slack(x)
        if np.any(s <= 0):
            return np.full_like(x, np.nan)
        return self.c + self.Am.T @ (1.0 / s)

    def hess(self, x):
        s = self.slack(x)
        return (self.Am.T / s**2) @ self.Am

    def hvp(self, x, v):
        s = self.slack(x)
        if np.any(s <= 0):
            return np.full_like(x, np.nan)
        return self.Am.T @ ((self.Am @ v) / s**2)

    def newton(self, x):
        for _ in range(200):
            g = self.grad(x)
            H = self.hess(x)
            dx = np.linalg.solve(H, g)
            lam = np.sqrt(g @ dx)
            t = 1.0 if lam < 0.25 else 1.0 / (1.0 + lam)
            x = x - t * dx
            if lam < 1e-15:
                break
        return x
