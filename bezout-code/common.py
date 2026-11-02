"""Chebyshev iterations, scalar preparation and physical oracle responses."""

import math
from decimal import Decimal, localcontext
from functools import lru_cache

import numpy as np

ADDITIVE = ("flat", "pref", "lf", "dfb", "masg")
VARIATION = ("balanced", "pref", "lf", "sine")
NAME = {
    "flat": "Flat",
    "balanced": "Balanced",
    "pref": "Prefix",
    "lf": "LF/fractal",
    "dfb": "DFB",
    "masg": "M-ASG",
    "sine": "Sine–Jacobi",
}


def epsilon(N, mu, L):
    z = N * math.acosh((L + mu) / (L - mu))
    return 2 * math.exp(-z) / (1 + math.exp(-2 * z))


def fractal_order(N):
    if N < 1 or N & (N - 1):
        raise ValueError("The published LF/fractal ordering requires N=2^k.")
    p = [1]
    while len(p) < N:
        n = 2 * len(p)
        p = [v for j in p for v in (j, n + 1 - j)]
    return np.array(p) - 1


def _cheb(z, N, second=False):
    p = [Decimal(1), 2 * z if second else z]
    for _ in range(2, N + 1):
        p.append(2 * z * p[-1] - p[-2])
    return p[: N + 1]


@lru_cache(maxsize=24)
def prepare(method, N, mu, L):
    """Scalar coefficients only; O(N) work/storage, fixed before oracle calls."""
    if N < 2 or not 0 < mu < L:
        raise ValueError("Require N>=2, 0<mu<L.")
    d = {"method": method, "N": N, "mu": mu, "L": L}
    with localcontext() as ctx:
        ctx.prec = 80
        lo, hi = Decimal(str(mu)), Decimal(str(L))
        D, eta = hi - lo, (hi + lo) / (hi - lo)
        C = _cheb(eta, N)
        if method == "flat":
            u = _cheb(eta, N, True)
            mass = [u[N - 1] / 2] + [u[N - 1 - j] for j in range(1, N)]
            delta = sum(mass) / N
            total, R = Decimal(0), []
            for m in range(N):
                total += mass[m]
                R.append(total - m * delta)
            tau = np.array([float(R[N - 1 - s] / delta - 1) for s in range(N)])
            tau[0] = 0.0
            d.update(
                tau=tau,
                invu=np.array([float(1 / v) for v in u]),
                mix=np.array([float(mass[m] / R[m]) for m in range(N)]),
                scale=float(-4 * delta / (D * C[N])),
                alpha=np.array(
                    [
                        float(2 / (lo + hi) if s == 0 else 4 * u[s] / (D * u[s + 1]))
                        for s in range(N - 1)
                    ]
                ),
                beta=np.array(
                    [
                        0.0 if s == 0 else float(u[s - 1] / u[s + 1])
                        for s in range(N - 1)
                    ]
                ),
                last_a=float(u[N - 2] / C[N]),
                last_b=float(2 * u[N - 1] / (D * C[N])),
            )
        elif method == "balanced":
            w = [Decimal(1)] * N
            Z = [Decimal(1), eta] + [Decimal(0)] * (N - 2)
            for s in range(2, N):
                w[s] = (
                    Decimal(N + 2 - s - s % 2) / N
                    if N % 2 == 0
                    else Decimal((N + 1) * (N + 1 - s)) / (N * N + 1)
                    if s % 2 == 0
                    else Decimal(N + 2 - s) / (N + 1)
                )
                Z[s] = Z[s - 2] + w[s] * (C[s] - C[s - 2])
            b = [Decimal(0)] * N
            for parity in (0, 1):
                P = Q = Decimal(0)
                for s in reversed(range(parity, N, 2)):
                    P += (1 if N - 1 - s == 0 else 2) * C[N - 1 - s]
                    R = Q + (1 if s == 0 else 2) * P / 2
                    b[s] = (
                        4
                        * Z[s]
                        / (D * C[N])
                        * (R / w[s] - (Q / w[s + 2] if s + 2 < N else 0))
                    )
                    Q = R
            # Normalized Q,W recurrence from Eq. (W) in the proof. It gives
            # exactly the same history as the four-prediction pseudocode.
            W = np.zeros((N, 5))
            for s in range(2, N - 1):
                W[s] = [
                    float(2 * eta * Z[s] / Z[s + 1]),
                    float(-Z[s - 1] / Z[s + 1]),
                    float(-4 * Z[s] / (D * w[s] * Z[s + 1])),
                    float(4 * Z[s - 2] / (D * w[s] * Z[s + 1])),
                    float(Z[s - 1] / Z[s + 1]),
                ]
            start = (
                [
                    float(2 * (eta * eta - 1) / Z[2]),
                    float(-4 * eta / (D * Z[2])),
                    float(1 / Z[2]),
                ]
                if N > 2
                else []
            )
            d.update(
                w=np.array(list(map(float, w))),
                invZ=np.array([float(1 / v) for v in Z]),
                scale=np.array([float(-4 * v / (D * C[N])) for v in Z]),
                b=np.array(list(map(float, b))),
                W=W,
                start=start,
                first=float(2 / (D * eta)),
            )
        else:
            alpha, beta = np.empty(N), np.zeros(N)
            reset = np.zeros(N, bool)
            if method == "lf":
                j = fractal_order(N)
                alpha[:] = 1 / (
                    (L + mu) / 2 - (L - mu) / 2 * np.cos((j + 0.5) * np.pi / N)
                )
            elif method == "sine":
                ratio = eta
                alpha[0] = float(2 / (D * ratio))
                for s in range(1, N):
                    t = math.pi * s / N
                    half = math.pi / (2 * N)
                    coupling = Decimal(
                        str(
                            math.sin(t) ** 2
                            / (4 * math.sin(t - half) * math.sin(t + half))
                        )
                    )
                    nxt = eta - coupling / ratio
                    beta[s], alpha[s] = (
                        float(coupling / (ratio * nxt)),
                        float(2 / (D * nxt)),
                    )
                    ratio = nxt
            elif method == "pref":
                for s in range(N):
                    alpha[s] = float(
                        2 / (lo + hi) if s == 0 else 4 * C[s] / (D * C[s + 1])
                    )
                    beta[s] = 0.0 if s == 0 else float(C[s - 1] / C[s + 1])
            elif method == "dfb":
                alpha.fill(1 / L)
                beta.fill(1.0)
            elif method == "masg":
                stage, left, B = (
                    1,
                    max(1, N // 2),
                    math.ceil(3 * math.sqrt(L / mu) * math.log(2)),
                )
                for s in range(N):
                    if left == 0:
                        stage += 1
                        left = 2**stage * B
                        reset[s] = True
                    alpha[s] = 1 / L if stage == 1 else 1 / (4**stage * L)
                    q = math.sqrt(mu * alpha[s])
                    beta[s] = (1 - q) / (1 + q)
                    left -= 1
            else:
                raise ValueError(method)
            d.update(alpha=alpha, beta=beta, reset=reset)
    return d


def run(c, x0, oracle):
    """One direct finite-memory run; exactly N calls, always from x0."""
    name, N = c["method"], c["N"]
    if name == "flat":
        V, P, G = x0.copy(), x0.copy(), np.zeros_like(x0)
        for s, t in enumerate(c["tau"]):
            g = oracle((1 + t) * V - t * P, s)
            G = (g + t * G) / (1 + t)
            if s == N - 1:
                return (1 + c["last_a"]) * V - c["last_a"] * P - c["last_b"] * G
            V, P = (1 + c["beta"][s]) * V - c["beta"][s] * P - c["alpha"][s] * G, V
    if name == "balanced":
        X = x0.copy()
        correction = np.zeros_like(x0)

        def accumulate(g, s):
            nonlocal X, correction
            term = -c["b"][s] * g - correction
            new = X + term
            correction = (new - X) - term
            X = new

        g0 = oracle(x0, 0)
        accumulate(g0, 0)
        previous = x0 - c["first"] * g0
        g1 = oracle(previous, 1)
        accumulate(g1, 1)
        if N == 2:
            return X
        a, b, d = c["start"]
        v = a * x0 + b * (g0 + g1)
        old_v = np.zeros_like(x0)
        query = d * x0 + c["w"][2] * v
        old_g, g_previous = g0, g1
        for s in range(2, N):
            g = oracle(query, s)
            accumulate(g, s)
            if s + 1 < N:
                a, b, d, e, f = c["W"][s]
                next_v = a * v + b * old_v + d * g + e * old_g
                previous, query = query, f * previous + c["w"][s + 1] * next_v
                old_v, v = v, next_v
                old_g, g_previous = g_previous, g
        return X
    x, previous = x0.copy(), x0.copy()
    average = x0.copy()
    for s, (alpha, beta) in enumerate(zip(c["alpha"], c["beta"])):
        if c["reset"][s]:
            previous = x.copy()
        query = (1 + beta) * x - beta * previous if name in ("dfb", "masg") else x
        nxt = (1 + beta) * x - beta * previous - alpha * oracle(query, s)
        previous, x = x, nxt
        if name == "dfb":
            average += (x - average) / (s + 2)
    return average if name == "dfb" else x


def responses(c, lam):
    """p_N(lambda), nominal queries pi_s, physical responses Phi_s."""
    lam = np.atleast_1d(lam).astype(float)
    N = c["N"]
    mu, L = c["mu"], c["L"]
    z = (L + mu - 2 * lam) / (L - mu)
    T = np.empty((N + 1, len(lam)))
    U = np.empty_like(T)
    T[0], T[1] = 1.0, z
    U[0], U[1] = 1.0, 2 * z
    for j in range(2, N + 1):
        T[j] = 2 * z * T[j - 1] - T[j - 2]
        U[j] = 2 * z * U[j - 1] - U[j - 2]
    p = epsilon(N, mu, L) * T[N]
    if c["method"] == "flat":
        q = (1 + c["tau"][:, None]) * U[:N] * c["invu"][:N, None]
        q[1:] -= c["tau"][1:, None] * U[: N - 1] * c["invu"][: N - 1, None]
        H = np.ones_like(q)
        for j in range(1, N):
            H[j] = (1 - c["mix"][j]) * H[j - 1] + c["mix"][j] * T[j]
        return p, q, c["scale"] * H[::-1]
    if c["method"] == "balanced":
        psi = T[:N].copy()
        for s in range(2, N):
            psi[s] = psi[s - 2] + c["w"][s] * (T[s] - T[s - 2])
        q = psi * c["invZ"][:, None]
        phi = np.zeros_like(q)
        for parity in (0, 1):
            P = np.zeros(len(lam))
            Q = np.zeros(len(lam))
            for s in reversed(range(parity, N, 2)):
                P += (1 if N - 1 - s == 0 else 2) * T[N - 1 - s]
                R = Q + (1 if s == 0 else 2) * P / 2
                F = R / c["w"][s] - (Q / c["w"][s + 2] if s + 2 < N else 0)
                phi[s] = c["scale"][s] * F
                Q = R
        return p, q, phi
    x = np.ones(len(lam))
    old = x.copy()
    q = []
    states = [x.copy()]
    a = []
    b = []
    for s, (alpha, beta) in enumerate(zip(c["alpha"], c["beta"])):
        if c["reset"][s]:
            old = x.copy()
        query = (1 + beta) * x - beta * old if c["method"] in ("dfb", "masg") else x
        q.append(query.copy())
        extrap = c["method"] in ("dfb", "masg")
        aa = (1 - alpha * lam) * (1 + beta) if extrap else 1 + beta - alpha * lam
        bb = -(1 - alpha * lam) * beta if extrap else np.full(len(lam), -beta)
        if c["reset"][s]:
            aa = 1 - alpha * lam
            bb = np.zeros_like(lam)
        a.append(aa)
        b.append(bb)
        x, old = (1 + beta) * x - beta * old - alpha * lam * query, x
        states.append(x.copy())
    q = np.array(q)
    if c["method"] == "dfb":
        states = np.array(states)
        return states.mean(axis=0), q, -(1 - states[N:0:-1]) / ((N + 1) * lam)
    phi = np.empty((N, len(lam)))
    w0 = np.ones(len(lam))
    w1 = np.zeros(len(lam))
    for s in reversed(range(N)):
        phi[s] = -c["alpha"][s] * w0
        w0, w1 = w0 * a[s] + w1, w0 * b[s]
    return (x if c["method"] == "masg" else p), q, phi
